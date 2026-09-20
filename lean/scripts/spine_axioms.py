#!/usr/bin/env python3
"""Spine axiom probe: report the axioms that the closed-form assembly theorem
`Kepler.Assembly.the_kepler_conjecture_from_interfaces` depends on.

This is the Phase 6 "reachable debt" meter: unlike the raw `sorry` token count
in DEBT.md (which counts placeholders anywhere in the tree), this probe asks
the kernel which axioms the *assembled main theorem* actually rests on.

Output is a Markdown fragment intended for embedding into DEBT.md by
`debt_ledger.py --with-spine`.

Consistency design (2026-09-20): the main repo's .lake cache is built from
opencode's *wip working tree* and drifts daily (even mid-build inconsistent).
So the probe does NOT trust cached Kepler oleans outside the stable Phase 2
subtree: modules under Kepler/Graphs (frozen, native_decide shards) are
symlinked from the cache; every other Kepler module in Assembly's transitive
import closure is compiled from THIS worktree's sources.  Results are cached
in /home/scroll/spine-cache/<main-sha>/ so repeat runs on an unchanged main
are instant (oleans + fragment persisted).

Usage:  python3 lean/scripts/spine_axioms.py [repo_root]
Requires: elan toolchain + a populated .lake (OLEAN cache) under lean/.
"""
import os
import re
import subprocess
import sys
import datetime

ROOT = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEAN_DIR = os.path.join(ROOT, "lean")
PROBE = ".spine_probe.lean"
TARGET = "Kepler.Assembly.the_kepler_conjecture_from_interfaces"
CACHE_ROOT = "/home/scroll/spine-cache"

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
# DECISIONS.md 2026-08-10 scoped exception: native_decide 证书公理，
# 形态为 Lean.ofReduceBool 或逐 shard 的 `*_native.native_decide.ax_*`。
SHARD_AX = re.compile(r"_native\.native_decide\.ax_")

IMPORT_RE = re.compile(r"^import\s+(Kepler[\w.]*)", re.M)
# 稳定子树：Phase 2 图枚举（不再变动），其缓存 olean 可信。
TRUSTED_PREFIXES = ("Kepler/Graphs",)


def lean_binary():
    tc = os.path.expanduser(
        "~/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean")
    return tc if os.path.exists(tc) else "lean"


def head_sha():
    return subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                          capture_output=True, text=True,
                          check=True).stdout.strip()


def base_env():
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + env["PATH"]
    lp = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"],
                        cwd=LEAN_DIR, env=env, capture_output=True,
                        text=True, check=True).stdout.strip()
    return env, lp


def closure(root_mod):
    """Transitive Kepler imports of root_mod, dependency-first order."""
    order, seen = [], set()

    def visit(name):
        if name in seen:
            return
        seen.add(name)
        src = os.path.join(LEAN_DIR, *name.split(".")) + ".lean"
        if not os.path.exists(src):
            return
        with open(src, encoding="utf-8") as fh:
            for imp in IMPORT_RE.findall(fh.read()):
                visit(imp)
        order.append(name)

    visit(root_mod)
    return order


def build_closure(lp, olean_dir):
    """Compile the closure into olean_dir: Graphs symlinked from the build
    cache, everything else compiled from worktree sources.  Returns (log, ok).
    Idempotent: existing oleans are reused (dir is keyed by main sha)."""
    env, _ = base_env()
    env["LEAN_PATH"] = olean_dir + ":" + lp
    out = ""
    # Graphs 子树做 symlink 林
    cached = None
    for entry in lp.split(":"):
        cand = os.path.join(entry, "Kepler", "Graphs")
        if os.path.isdir(cand):
            cached = cand
            break
    if cached:
        dst = os.path.join(olean_dir, "Kepler", "Graphs")
        # 顶层模块文件 Kepler/Graphs.olean 等（与子目录同级）也要链接
        parent = os.path.dirname(cached)
        kroot = os.path.join(olean_dir, "Kepler")
        os.makedirs(kroot, exist_ok=True)
        for f in os.listdir(parent):
            if f.startswith("Graphs."):
                link = os.path.join(kroot, f)
                if os.path.islink(link) and not os.path.exists(link):
                    os.remove(link)
                if not os.path.exists(link):
                    os.symlink(os.path.join(parent, f), link)
        for dirpath, _, filenames in os.walk(cached):
            rel = os.path.relpath(dirpath, cached)
            out_dir = dst if rel == "." else os.path.join(dst, rel)
            os.makedirs(out_dir, exist_ok=True)
            for f in filenames:
                link = os.path.join(out_dir, f)
                if os.path.islink(link) and not os.path.exists(link):
                    os.remove(link)
                if not os.path.exists(link):
                    os.symlink(os.path.join(dirpath, f), link)
    for name in closure(TARGET.rsplit(".", 1)[0]):
        rel = "/".join(name.split("."))
        if any(rel.startswith(p) for p in TRUSTED_PREFIXES):
            continue  # symlink 已覆盖
        ol = os.path.join(olean_dir, rel + ".olean")
        src = os.path.join(LEAN_DIR, rel + ".lean")
        if os.path.exists(ol) and os.path.getmtime(ol) >= os.path.getmtime(src):
            continue
        os.makedirs(os.path.dirname(ol), exist_ok=True)
        proc = subprocess.run([lean_binary(), "-o", ol, src],
                              cwd=LEAN_DIR, env=env, capture_output=True,
                              text=True, timeout=7200)
        out += proc.stdout + proc.stderr
        if proc.returncode != 0 or not os.path.exists(ol):
            return out, False
    return out, True


def main():
    sha = head_sha()
    cache = os.path.join(CACHE_ROOT, sha)
    frag = os.path.join(cache, "fragment.md")
    if os.path.exists(frag):
        with open(frag, encoding="utf-8") as fh:
            print(fh.read())
        return 0
    os.makedirs(cache, exist_ok=True)
    env, lp = base_env()
    olean_dir = os.path.join(cache, "oleans")
    out, ok = build_closure(lp, olean_dir)
    if not ok:
        return report_failure(out)
    probe = os.path.join(LEAN_DIR, PROBE)
    with open(probe, "w", encoding="utf-8") as fh:
        fh.write(f"import Kepler.Assembly\n#print axioms {TARGET}\n")
    try:
        env2 = dict(env, LEAN_PATH=olean_dir + ":" + lp)
        proc = subprocess.run([lean_binary(), probe], cwd=LEAN_DIR, env=env2,
                              capture_output=True, text=True, timeout=7200)
        out = proc.stdout + proc.stderr
    finally:
        try:
            os.remove(probe)
        except OSError:
            pass
    m = re.search(r"depends on axioms:\s*\[([^\]]*)\]", out)
    if not m:
        return report_failure(out)
    axioms = {a.strip() for a in m.group(1).split(",") if a.strip()}

    def is_sanctioned(a):
        return a in {"Lean.ofReduceBool", "Lean.trustCompiler"} or SHARD_AX.search(a)

    debt = sorted(a for a in axioms if a == "sorryAx")
    sanctioned = sorted(a for a in axioms if is_sanctioned(a))
    standard = sorted(axioms & STANDARD)
    other = sorted(a for a in axioms
                   if a not in STANDARD and a != "sorryAx"
                   and not is_sanctioned(a))
    ts = datetime.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M %z")
    lines = []
    lines.append("\n## 主定理可达债务（脊柱公理探针）\n")
    lines.append(f"> `{TARGET}` 的 `#print axioms`，探针运行时间 {ts}（main @ {sha[:8]}，全闭包自主源编译）。")
    lines.append("> 与上面的 token 计数不同：这里只统计**装配后主定理实际依赖**的公理。\n")
    lines.append("| 类别 | 公理 |")
    lines.append("|---|---|")
    lines.append(f"| sorry 占位（接口债务） | {', '.join(debt) or '**无**'} |")
    lines.append(f"| 特许 native_decide（DECISIONS.md 2026-08-10 scoped exception） "
                 f"| {len(sanctioned)} 个 shard 公理 / ofReduceBool 族 |")
    lines.append(f"| 标准三公理 | {', '.join(standard) or '无'} |")
    lines.append(f"| 其它（**异常，需排查**） | {', '.join(other) or '无'} |")
    lines.append("")
    if debt:
        lines.append("`sorryAx` 当前来源 = Assembly.lean 的冻结接口占位"
                     "（剩余 `nonlinearInequalities` / `linearProgrammingResults` /"
                     " `textCapstone` 三个；`goodListArchive` 已于 2026-09-19 由 P6-C 闭合，"
                     "见 docs/phase6-spine.md §1）；每闭合一个接口，此处可达债务随之消减。")
    text = "\n".join(lines)
    with open(frag, "w", encoding="utf-8") as fh:
        fh.write(text)
    print(text)
    return 0


def report_failure(out):
    ts = datetime.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M %z")
    print("\n## 主定理可达债务（脊柱公理探针）\n")
    print(f"> 探针于 {ts} 运行失败，本节无数据。输出尾部：\n")
    print("```")
    print("\n".join(out.splitlines()[-15:]))
    print("```")
    return 1


if __name__ == "__main__":
    sys.exit(main())
