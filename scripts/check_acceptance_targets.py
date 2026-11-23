#!/usr/bin/env python3
"""验收 target 静态自检（P0-1，eng-acceptance-gate-w1，2026-11-23 用户明批）。

零编译、零 lake、只读。断言：
1. `lean/lakefile.toml` 存在一个 `[[lean_lib]]`，其 `roots` 含 `"Kepler.Final"`
   （即命名验收 target `KeplerAcceptance`）；
2. `defaultTargets` 仍是 `["Kepler"]`——P0-1 明确不改 defaultTargets；
3. `lean/Kepler/Final.lean` 存在且含根定理探针
   `#print axioms ... the_kepler_conjecture_e2e`（唯一验收语言，AGENTS §1/§5）；
4. 验收文档三处注明验收 root：`AGENTS.md` §5、`docs/tools.md` §4、`Makefile`；
5. 遗留入口隔离（P0-2）：`Makefile` 的 build/check/reprove 是闸门（exit 1），
   `*.legacy-unsafe` 仅考古；`.github/workflows/ci.yml` 无 `lake build` 且只在
   `workflow_dispatch` 触发；`lean/scripts/AxiomAudit.lean` 含根面探针；
6. import 图（纯静态）：报告 `Kepler.Final` 的 import 闭包规模，并断言它不在
   defaultTargets 闭包内（这正是 P0-1 的问题证据：default build 成功 ≠ 验收）。

退出码：0 = 全部断言通过；1 = 任一失败。CI 静态闸直接调用本脚本。
"""
from __future__ import annotations

import os
import re
import sys

try:
    import tomllib
except ModuleNotFoundError:  # Python < 3.11
    sys.exit("ERROR: 需要 Python >= 3.11（tomllib）")

BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.'«»]+)", re.M)
ROOT_PROBE = "the_kepler_conjecture_e2e"

FAILS: list[str] = []


def read(path: str) -> str:
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        return f.read()


def check(name: str, ok: bool, detail: str = "") -> None:
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" —— {detail}" if detail else ""))
    if not ok:
        FAILS.append(name)


def main() -> int:
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

    # ---- 1/2 lakefile ----
    lf_path = os.path.join(repo, "lean", "lakefile.toml")
    with open(lf_path, "rb") as f:
        lf = tomllib.load(f)
    libs = lf.get("lean_lib", [])
    acc = [lib for lib in libs if "Kepler.Final" in (lib.get("roots") or [])]
    check("lakefile 存在 roots 含 Kepler.Final 的 lean_lib（KeplerAcceptance）",
          bool(acc), "; ".join(lib.get("name", "?") for lib in acc) or "无")
    default_targets = lf.get("defaultTargets")
    check("defaultTargets 未改（== [\"Kepler\"]）", default_targets == ["Kepler"],
          f"当前 = {default_targets}")
    acc_names = [lib.get("name") for lib in acc]
    check("验收 target 名为 KeplerAcceptance", acc_names == ["KeplerAcceptance"],
          f"当前 = {acc_names}")

    # ---- 3 根文件与探针 ----
    final_path = os.path.join(repo, "lean", "Kepler", "Final.lean")
    ok_final = os.path.isfile(final_path)
    check("lean/Kepler/Final.lean 存在", ok_final)
    if ok_final:
        final_text = read(final_path)
        probe_ok = re.search(r"#print\s+axioms\s+(?:\w+\.)?%s\b" % ROOT_PROBE,
                             final_text) is not None
        check("Final.lean 含根定理 #print axioms 探针", probe_ok, ROOT_PROBE)

    # ---- 4 验收文档三处注明 ----
    agents = read(os.path.join(repo, "AGENTS.md"))
    tools = read(os.path.join(repo, "docs", "tools.md"))
    makefile = read(os.path.join(repo, "Makefile"))
    sec5 = agents.split("## 5.", 1)[-1].split("## 6.", 1)[0]
    check("AGENTS.md §5 注明验收 root = Kepler.Final",
          "Kepler.Final" in sec5 and "KeplerAcceptance" in sec5)
    tools_s4 = tools.split("## 4.", 1)[-1].split("## 5.", 1)[0]
    check("docs/tools.md §4 注明验收 root = Kepler.Final",
          "Kepler.Final" in tools_s4 and "KeplerAcceptance" in tools_s4)
    check("Makefile 注明验收 root = Kepler.Final",
          "Kepler.Final" in makefile and "KeplerAcceptance" in makefile)

    # ---- 5 遗留入口隔离（P0-2） ----
    guard_ok = ("禁止全树构建" in makefile and "exit 1" in makefile
                and "legacy-unsafe" in makefile)
    check("Makefile build/check/reprove 为闸门（exit 1）且保留 *-legacy-unsafe",
          guard_ok)
    ci_path = os.path.join(repo, ".github", "workflows", "ci.yml")
    ci = read(ci_path)
    check("ci.yml 不再包含 lake build", "lake build" not in ci)
    on_block = ci.split("on:", 1)[1].split("jobs:", 1)[0]
    check("ci.yml 仅 workflow_dispatch 触发",
          "workflow_dispatch" in on_block and "push:" not in on_block
          and "pull_request:" not in on_block)
    audit_path = os.path.join(repo, "lean", "scripts", "AxiomAudit.lean")
    audit = read(audit_path)
    check("AxiomAudit.lean 含根面探针",
          re.search(r"#print\s+axioms\s+(?:\w+\.)?%s\b" % ROOT_PROBE, audit)
          is not None, audit_path)

    # ---- 6 import 图 ----
    lean_dir = os.path.join(repo, "lean")
    mod2imports: dict[str, list[str]] = {}
    mods: set[str] = set()
    for dirpath, dirnames, filenames in os.walk(lean_dir):
        dirnames[:] = [d for d in dirnames if d not in (".lake", ".git", "_distfiles")]
        for fn in filenames:
            if not fn.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dirpath, fn), lean_dir)
            mod = rel[:-5].replace(os.sep, ".")
            mods.add(mod)
            mod2imports[mod] = IMPORT_RE.findall(
                BLOCK_COMMENT.sub("", read(os.path.join(dirpath, fn))))
    # 第二遍过滤内部边（第一遍收集全部模块名后）
    for mod in mod2imports:
        mod2imports[mod] = [m for m in mod2imports[mod] if m in mods]

    def closure(start: str) -> set[str]:
        seen: set[str] = set()
        stack = [start]
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            seen.add(m)
            stack.extend(mod2imports.get(m, []))
        return seen

    final_mod = "Kepler.Final"
    check("import 图中存在模块 Kepler.Final", final_mod in mods)
    cone = closure(final_mod)
    check("Kepler.Final import 闭包规模 ≥ 1000 模块", len(cone) >= 1000,
          f"closure = {len(cone)}")
    default_cone = closure("Kepler") if "Kepler" in mods else set()
    check("Kepler.Final 不在 defaultTargets（Kepler）闭包内 —— default build ≠ 验收",
          final_mod not in default_cone,
          f"default closure = {len(default_cone)}, Final closure = {len(cone)}")

    rc = 1 if FAILS else 0
    print(f"CHECK {'FAIL' if FAILS else 'PASS'}（{len(FAILS)} 条 FAIL）")
    return rc


if __name__ == "__main__":
    sys.exit(main())
