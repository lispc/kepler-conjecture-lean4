#!/usr/bin/env python3
"""Spine axiom probe: report the axioms that the closed-form assembly theorem
`Kepler.Assembly.the_kepler_conjecture_from_interfaces` depends on.

This is the Phase 6 "reachable debt" meter: unlike the raw `sorry` token count
in DEBT.md (which counts placeholders anywhere in the tree), this probe asks
the kernel which axioms the *assembled main theorem* actually rests on.

Output is a Markdown fragment intended for embedding into DEBT.md by
`debt_ledger.py --with-spine`.

Assembly.lean is deliberately NOT imported by the Kepler root module, so its
olean is not in the normal build cache.  Lean pins all modules of a top-level
namespace to the first LEAN_PATH entry containing that directory, so we build
an overlay dir `lean/oleans/Kepler/`: symlinks to every cached Kepler olean
plus locally compiled oleans for modules missing from the cache (Assembly
itself and its discharge shard modules), compiled in dependency order.

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
OLEAN_DIR = os.path.join(LEAN_DIR, "oleans")
PROBE = os.path.join(LEAN_DIR, ".spine_probe.lean")
TARGET = "Kepler.Assembly.the_kepler_conjecture_from_interfaces"

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
# DECISIONS.md 2026-08-10 scoped exception: native_decide 证书公理，
# 形态为 Lean.ofReduceBool 或逐 shard 的 `*_native.native_decide.ax_*`。
SHARD_AX = re.compile(r"_native\.native_decide\.ax_")

IMPORT_RE = re.compile(r"^import\s+(Kepler[\w.]*)", re.M)


def lean_binary():
    tc = os.path.expanduser(
        "~/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean")
    return tc if os.path.exists(tc) else "lean"


def base_env():
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + env["PATH"]
    lp = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"],
                        cwd=LEAN_DIR, env=env, capture_output=True,
                        text=True, check=True).stdout.strip()
    return env, lp


def build_overlay(lp):
    """Symlink-forest overlay of the cached Kepler oleans into OLEAN_DIR.

    Adds symlinks for cached oleans; never touches real files (locally
    compiled modules such as the Assembly.* discharge shards)."""
    cached = None
    for entry in lp.split(":"):
        cand = os.path.join(entry, "Kepler")
        if os.path.isdir(cand):
            cached = cand
            break
    if cached is None:
        raise RuntimeError("no cached Kepler oleans found in LEAN_PATH")
    dst = os.path.join(OLEAN_DIR, "Kepler")
    os.makedirs(dst, exist_ok=True)
    for dirpath, _, filenames in os.walk(cached):
        rel = os.path.relpath(dirpath, cached)
        out_dir = dst if rel == "." else os.path.join(dst, rel)
        os.makedirs(out_dir, exist_ok=True)
        for f in filenames:
            link = os.path.join(out_dir, f)
            if os.path.islink(link) and not os.path.exists(link):
                os.remove(link)  # stale symlink
            if not os.path.exists(link):
                os.symlink(os.path.join(dirpath, f), link)


def mod_src(name):
    return os.path.join(LEAN_DIR, *name.split(".")) + ".lean"


def mod_oleans(name):
    return os.path.join(OLEAN_DIR, *name.split(".")) + ".olean"


def collect_missing(root_mod):
    """Transitive Kepler imports of root_mod whose olean is absent/stale,
    in dependency-first (topological) order."""
    order, seen = [], set()

    def visit(name):
        if name in seen:
            return
        seen.add(name)
        src = mod_src(name)
        if not os.path.exists(src):
            return  # not a workspace module (cached-only or external)
        with open(src, encoding="utf-8") as fh:
            for imp in IMPORT_RE.findall(fh.read()):
                visit(imp)
        ol = mod_oleans(name)
        stale = (not os.path.exists(ol)) or (
            not os.path.islink(ol)
            and os.path.getmtime(ol) < os.path.getmtime(src))
        if stale:
            order.append(name)

    visit(root_mod)
    return order


def build_chain(lp, root_mod="Kepler.Assembly"):
    """Compile missing/stale dependency oleans into the overlay, dep-first.

    Returns (log, ok)."""
    env, _ = base_env()
    env["LEAN_PATH"] = OLEAN_DIR + ":" + lp
    out = ""
    for name in collect_missing(root_mod):
        os.makedirs(os.path.dirname(mod_oleans(name)), exist_ok=True)
        proc = subprocess.run([lean_binary(), "-o", mod_oleans(name),
                               mod_src(name)], cwd=LEAN_DIR, env=env,
                              capture_output=True, text=True, timeout=7200)
        out += proc.stdout + proc.stderr
        if proc.returncode != 0 or not os.path.exists(mod_oleans(name)):
            return out, False
    return out, True


def main():
    env, lp = base_env()
    try:
        build_overlay(lp)
    except Exception as e:  # overlay failure -> report, no probe
        return report_failure(f"overlay build failed: {e}")
    # 1. compile missing dependency oleans (Assembly + discharge shards)
    out, ok = build_chain(lp)
    if not ok:
        return report_failure(out)
    # 2. probe
    with open(PROBE, "w", encoding="utf-8") as fh:
        fh.write(f"import Kepler.Assembly\n#print axioms {TARGET}\n")
    try:
        env2 = dict(env, LEAN_PATH=OLEAN_DIR + ":" + lp)
        proc = subprocess.run([lean_binary(), PROBE], cwd=LEAN_DIR, env=env2,
                              capture_output=True, text=True, timeout=7200)
        out = proc.stdout + proc.stderr
    finally:
        try:
            os.remove(PROBE)
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
    print("\n## 主定理可达债务（脊柱公理探针）\n")
    print(f"> `{TARGET}` 的 `#print axioms`，探针运行时间 {ts}。")
    print("> 与上面的 token 计数不同：这里只统计**装配后主定理实际依赖**的公理。\n")
    print("| 类别 | 公理 |")
    print("|---|---|")
    print(f"| sorry 占位（接口债务） | {', '.join(debt) or '**无**'} |")
    print(f"| 特许 native_decide（DECISIONS.md 2026-08-10 scoped exception） "
          f"| {len(sanctioned)} 个 shard 公理 / ofReduceBool 族 |")
    print(f"| 标准三公理 | {', '.join(standard) or '无'} |")
    print(f"| 其它（**异常，需排查**） | {', '.join(other) or '无'} |")
    print()
    if debt:
        print("`sorryAx` 当前来源 = Assembly.lean 的冻结接口占位"
              "（剩余 `nonlinearInequalities` / `linearProgrammingResults` /"
              " `textCapstone` 三个；`goodListArchive` 已于 2026-09-19 由 P6-C 闭合，"
              "见 docs/phase6-spine.md §1）；每闭合一个接口，此处可达债务随之消减。")
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
