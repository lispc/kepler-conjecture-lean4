#!/usr/bin/env python3
"""sorry census — 只读静态扫描本仓全部 Lean 源文件中的 `sorry`。

来源与口径（工单 eng-acceptance-gate-w1 / P0-3，用户 2026-11-23 明批）：
- 规格正本：`~/c17_backup/lane_snapshots/lean4-large-project-practices-w1/`
  `evidence/recommendations.tsv` 的 P0-3 行；口径依据同目录 REPORT.md §2.4/§2.5。
- token 口径 = practices `profile_repo.py` 同款：walk `lean/`（跳过 .lake/.git/
  _distfiles），块注释按非贪婪正则 `/-.*?-/` 整体移除后数 `\bsorry\b`；
  **行注释不移除**（即行注释里的 sorry 计入 token，本脚本单独标 kind=comment）。
- cone 口径 = 从模块 `Kepler.Final` 沿仓内 import 边（同一正则、同一种移除方式
  解析）的传递闭包；**import 锥 ⊋ proof-term 锥**，故本脚本 cone 数 ≥ 仪器
  `docs/e2e-reachability-map.tsv` 的 SORRIED 声明数，属预期。

四个总数（**口径 = 非 comment token**，即 practices `profile_repo.py`/`metrics_careful.py`
最终报告的口径；行注释里的 "sorry" 词在 TSV 中单列为 kind=comment，不计入四总数。
2026-11-23 在 6b5aa7da 树上逐文件复现 practices per_file_metrics.tsv 全表一致，
见 DELIVERY eng-acceptance-gate-w1）：
- cone-decl  = Final import 锥内含 ≥1 个非 comment sorry token 的**声明**数（去重）。
- cone-token = 锥内非 comment token 数（Text 444 + Assembly.lean 54 + Statement.lean 1）。
- repo-token = 全仓非 comment token 数（practices 实测 43,422）。
- LP-debt    = `lean/Kepler/Text/LP/` 目录内非 comment token 数（REPORT §2.2 实测
  42,889；该目录完全不在 Final import 锥内）。

`--check` 退出码语义：0 = 全部对账通过；1 = 任一 pin/对账失败。任何新增/删除
非 comment sorry 都会改变 token 总数从而触发非 0（即“新增 sorry 使 --check 非 0”）。
仪器 `docs/e2e-reachability-map.tsv` SORRIED 段 51 行是 AQ 基线 `e4c384e6` 时点的
stale 口径；本脚本要求其中每一名要么仍带静态 sorry、要么属于下方 EXEMPT_STALE_SORRIED
（wt2A 验收 `1ec06b28` 已证的 2 条）；并要求 Assembly 静态债声明不得超出
（仪器名单 ∪ ASM_STATIC_EXTRA_ALLOW）。

本脚本纯文本扫描，不做任何编译、不写除 `--out` 指定 TSV 之外的任何文件。
"""
from __future__ import annotations

import argparse
import bisect
import os
import re
import subprocess
import sys
from collections import Counter

# ---- 与 practices profile_repo.py 逐字同款的正则（口径复现的关键） ----
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)          # 非贪婪，嵌套块注释按非嵌套近似
SORRY_RE = re.compile(r"\bsorry\b")
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.'«»]+)", re.M)
SKIP_DIRS = {".lake", ".git", "_distfiles"}

NS_RE = re.compile(r"^[ \t]*namespace[ \t]+([A-Za-z0-9_.']+)[ \t]*$")
END_RE = re.compile(r"^[ \t]*end(?:[ \t]+([A-Za-z0-9_.']+))?[ \t]*$")
SECTION_RE = re.compile(r"^[ \t]*section(?:[ \t]+([A-Za-z0-9_.']+))?[ \t]*$")
# 顶层声明起始（含属性/修饰前缀；名字对 instance/example 可省略 → anon@行号）
DECL_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local|rec)[ \t]+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|example|axiom|opaque|class)"
    r"(?:[ \t]+([A-Za-z_][A-Za-z0-9_'!]*))?"
)
# 整条声明体恰为 `:= sorry`（stub 声明，kind=decl:=sorry）；`\s*` 容忍体后到下一
# 声明之间的空行。`:= by … sorry` 不匹配（by 介入）→ 仍归 proof:sorry。
STUB_RE = re.compile(r":=[ \t]*sorry\s*\Z", re.S)

FINAL_MODULE = "Kepler.Final"
LP_DIR_PREFIX = "Kepler/Text/LP/"

# ---- --check 基线 pin（口径 = 非 comment token） ----
# 三个 token pin 与 practices-w1 evidence/per_file_metrics.tsv 逐文件一致（基线树
# 6b5aa7da，2026-11-23，见车道 DELIVERY）；fs-walk 与 --tracked-only 在基线树上同值
# （untracked 文件的非 comment token 贡献为 0）。
# ERRATA（2026-11-26）：wt1 全量证书闭合 `4bcbd7ad` 把 `nliCell3QZECFICwt1` 的
# `:= sorry` 换成证明 ⇒ repo/cone 各 −1（43422→43421、499→498）；sorries 48 = 47 nli*
# + 1 hLP。该条仪器 SORRIED 仍在（地图是 AQ 基线 stale），入 EXEMPT_STALE_SORRIED。
EXPECT_REPO_TOKEN = 43421   # 基线 6b5aa7da 为 43422；wt1 闭合 −1
EXPECT_CONE_TOKEN = 498     # 基线 6b5aa7da 为 499；wt1 闭合 −1
EXPECT_LP_TOKEN = 42889     # 全在 Kepler/Text/LP/，不在 Final 锥内
# 仪器 SORRIED 行数（e2e-reachability-map.tsv = AQ 基线 e4c384e6 时点，stale）。
EXPECT_MAP_SORRIED = 51
# 显式豁免清单：仪器列出、但当前树已无静态 sorry 的声明名（= 仪器 stale 差额）。
# 依据：AGENTS §1 —— wt2A 小模块验收 `1ec06b28`（2026-11-20）后账本 49 = 48 nli*
# + 1 hLP；wt1 全量证书闭合 `4bcbd7ad`（2026-11-26）后 48 = 47 nli* + 1 hLP；
# 基线 e4c384e6 时为 51。census 实测恰好这 3 条无 sorry，独立复现 48。
EXEMPT_STALE_SORRIED: frozenset[str] = frozenset({
    "Kepler.Assembly.nliCell3QZECFICwt2A",
    "Kepler.Assembly.nliCell3QZECFICwt0sqrt8",
    "Kepler.Assembly.nliCell3QZECFICwt1",
})
# Assembly 静态债声明超出仪器名单的允许项：5 条 `*Ids` 清单侧同债形态
# （`theorem nli*Ids : AllCertified *Ids := sorry`；Assembly.lean §2a 注释
# “仍是同一债务的清单侧形态”）。仪器 SORRIED 不含它们（不计为独立 proof-term 债），
# 但它们带静态 sorry token —— 钉死名单，防止借同形声明新增债。
ASM_STATIC_EXTRA_ALLOW: frozenset[str] = frozenset({
    "Kepler.Assembly.nliKcblrqcIneqDefIds",
    "Kepler.Assembly.nliLpIneqsIds",
    "Kepler.Assembly.nliMainNonlinearTerminalV11Ids",
    "Kepler.Assembly.nliOx3q1hIds",
    "Kepler.Assembly.nliPackIneqDefAIds",
})


def mask_spans(text: str, spans: list[tuple[int, int]]) -> str:
    """把 spans 处内容替换成等长空格（保留换行符），保证 offset 与行号不变。"""
    chars = list(text)
    for a, b in spans:
        for i in range(a, b):
            if chars[i] != "\n":
                chars[i] = " "
    return "".join(chars)


def block_comment_spans(text: str) -> list[tuple[int, int]]:
    # 与 re.sub 的扫描语义一致（前一个匹配结束后继续找，不重叠）
    return [(m.start(), m.end()) for m in BLOCK_COMMENT.finditer(text)]


def mask_line_comments(text: str) -> str:
    """行注释 → 等长空格；带简单的字符串字面量保护（引号配对近似）。"""
    out = []
    for line in text.split("\n"):
        chars = list(line)
        i, n = 0, len(line)
        in_str = False
        while i < n:
            c = line[i]
            if in_str:
                if c == "\\":
                    i += 2
                    continue
                if c == '"':
                    in_str = False
                i += 1
                continue
            if c == '"':
                in_str = True
                i += 1
                continue
            if c == "-" and i + 1 < n and line[i + 1] == "-":
                for j in range(i, n):
                    chars[j] = " "
                break
            i += 1
        out.append("".join(chars))
    return "\n".join(out)


class Decl:
    __slots__ = ("start", "end", "fqn", "line")

    def __init__(self, start: int, end: int, fqn: str, line: int):
        self.start, self.end, self.fqn, self.line = start, end, fqn, line


def parse_decls(masked_all: str) -> list[Decl]:
    """在“块注释+行注释都置空”的文本上扫 namespace/section/end 与顶层声明。

    近似性（有意识接受，见 DELIVERY）：不解析字符串内的伪结构；声明体以下一个
    声明起始为界；结构体字段等缩进内容归入其宿主声明。
    """
    decls: list[Decl] = []
    stack: list[tuple[str, str | None]] = []  # (kind: ns|sec, name)
    offset = 0
    for idx, line in enumerate(masked_all.split("\n"), start=1):
        m = NS_RE.match(line)
        if m:
            stack.append(("ns", m.group(1)))
        else:
            m = SECTION_RE.match(line)
            if m:
                stack.append(("sec", m.group(1)))
            else:
                e = END_RE.match(line)
                if e:
                    name = e.group(1)
                    if name is None:
                        if stack:
                            stack.pop()
                    else:
                        for k in range(len(stack) - 1, -1, -1):
                            if stack[k][1] == name:
                                del stack[k:]
                                break
                else:
                    d = DECL_RE.match(line)
                    if d:
                        kw, name = d.group(1), d.group(2)
                        if not name:
                            name = f"anon@L{idx}"
                        ns_parts = [n for kind, n in stack if kind == "ns" and n]
                        fqn = ".".join(ns_parts + [name])
                        decls.append(Decl(offset, -1, fqn, idx))
        offset += len(line) + 1
    for i, d in enumerate(decls):
        d.end = decls[i + 1].start if i + 1 < len(decls) else len(masked_all)
    return decls


def body_upto_scope(decl: Decl, masked_all: str) -> str:
    """声明体切片截断到下一个 namespace/section/end 行之前——文件尾的
    `end Foo` 行不属于声明体，不能参与 `:= sorry` 的 stub 判定。"""
    body_lines = masked_all[decl.start : decl.end].split("\n")
    kept = []
    for i, line in enumerate(body_lines):
        if i and (NS_RE.match(line) or END_RE.match(line) or SECTION_RE.match(line)):
            break
        kept.append(line)
    return "\n".join(kept)


def scan_file(text: str) -> dict:
    """单文件扫描。返回 token 记录与口径计数。"""
    bspans = block_comment_spans(text)
    removed = BLOCK_COMMENT.sub("", text)           # practices 计数口径
    masked_blocks = mask_spans(text, bspans)        # token 定位/行号口径
    masked_all = mask_line_comments(masked_blocks)  # 注释判定 + 声明结构口径
    n_removed = len(SORRY_RE.findall(removed))
    tokens = []
    for m in SORRY_RE.finditer(masked_blocks):
        tokens.append(m.start())
    decls = parse_decls(masked_all)
    # token → 声明归属（decls 按 start 升序）
    starts = [d.start for d in decls]
    line_starts = [0]
    for line in masked_all.split("\n")[:-1]:
        line_starts.append(line_starts[-1] + len(line) + 1)

    def line_of(pos: int) -> int:
        return bisect.bisect_right(line_starts, pos)

    records = []
    for pos in tokens:
        li = bisect.bisect_right(starts, pos) - 1
        decl = decls[li] if li >= 0 else None
        body_slice = masked_all[decl.start : decl.end] if decl else ""
        # 行注释判定：masked_all 与 masked_blocks 的唯一差别是行注释被置空，
        # 故 token 处（原文非空格）在 masked_all 为空格 ⇔ 该 token 在行注释内。
        is_comment = masked_all[pos] == " "
        if is_comment:
            kind = "comment"
        elif decl is not None and STUB_RE.search(body_upto_scope(decl, masked_all)):
            kind = "decl:=sorry"
        else:
            kind = "proof:sorry"
        records.append(
            {
                "pos": pos,
                "line": line_of(pos),
                "decl": decl.fqn if decl else "-",
                "decl_line": decl.line if decl else None,
                "kind": kind,
            }
        )
    return {
        "n_removed": n_removed,
        "records": records,
        "decls": decls,
    }


def list_lean_files(lean_dir: str, tracked_only: bool) -> list[str]:
    if tracked_only:
        try:
            out = subprocess.run(
                ["git", "ls-files", "--", "lean"],
                cwd=os.path.dirname(lean_dir.rstrip("/")) or ".",
                capture_output=True, text=True, check=True,
            ).stdout
        except (OSError, subprocess.CalledProcessError) as exc:
            sys.exit(f"ERROR: --tracked-only 需要 git 仓库：{exc}")
        files = []
        for rel in out.splitlines():
            if rel.endswith(".lean") and rel.startswith("lean/"):
                p = os.path.join(os.path.dirname(lean_dir.rstrip("/")), rel)
                if os.path.isfile(p):
                    files.append(p)
        return sorted(files)
    files = []
    for dirpath, dirnames, filenames in os.walk(lean_dir):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for fn in filenames:
            if fn.endswith(".lean"):
                files.append(os.path.join(dirpath, fn))
    return sorted(files)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    here = os.path.dirname(os.path.abspath(__file__))
    repo_default = os.path.dirname(here)
    ap.add_argument("--repo", default=repo_default, help="仓库根目录（默认脚本上级）")
    ap.add_argument("--out", default=None,
                    help="TSV 输出路径（默认 <repo>/docs/sorry-census.tsv；--no-tsv 跳过）")
    ap.add_argument("--no-tsv", action="store_true", help="只打印汇总，不写 TSV")
    ap.add_argument("--tracked-only", action="store_true",
                    help="只数 git tracked 文件（默认 practices 口径 = 文件系统 walk，含 untracked）")
    ap.add_argument("--check", action="store_true",
                    help="对账模式：pin 基线总数 + 与 e2e-reachability-map.tsv SORRIED 段核对")
    ap.add_argument("--expect-repo-token", type=int, default=EXPECT_REPO_TOKEN)
    ap.add_argument("--expect-cone-token", type=int, default=EXPECT_CONE_TOKEN)
    ap.add_argument("--expect-lp-token", type=int, default=EXPECT_LP_TOKEN)
    args = ap.parse_args()

    lean_dir = os.path.join(args.repo, "lean")
    map_tsv = os.path.join(args.repo, "docs", "e2e-reachability-map.tsv")
    files = list_lean_files(lean_dir, args.tracked_only)
    if not files:
        sys.exit(f"ERROR: 在 {lean_dir} 没有找到 .lean 文件")

    mod2file: dict[str, str] = {}
    file2mod: dict[str, str] = {}
    for p in files:
        rel = os.path.relpath(p, lean_dir).replace(os.sep, "/")
        mod = rel[:-5].replace("/", ".")
        mod2file[mod] = rel
        file2mod[rel] = mod

    # import 图（practices 口径：块注释移除后按行首 import 解析，行注释不剥）
    imports: dict[str, list[str]] = {}
    texts: dict[str, str] = {}
    for p in files:
        rel = os.path.relpath(p, lean_dir).replace(os.sep, "/")
        with open(p, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
        texts[rel] = text
        imports[file2mod[rel]] = [
            m for m in IMPORT_RE.findall(BLOCK_COMMENT.sub("", text))
            if m in mod2file
        ]
    # Final import 闭包（含 Final 自身）
    cone_mods: set[str] = set()
    stack = [FINAL_MODULE]
    while stack:
        m = stack.pop()
        if m in cone_mods or m not in mod2file:
            continue
        cone_mods.add(m)
        stack.extend(imports.get(m, []))
    cone_files = {mod2file[m] for m in cone_mods}

    rows = []
    repo_token = 0
    parity_bad = []
    for p in files:
        rel = os.path.relpath(p, lean_dir).replace(os.sep, "/")
        r = scan_file(texts[rel])
        if r["n_removed"] != len(r["records"]):
            parity_bad.append((rel, r["n_removed"], len(r["records"])))
        repo_token += r["n_removed"]
        in_cone = rel in cone_files
        for rec in r["records"]:
            rows.append((rel, rec["line"], rec["decl"], in_cone, rec["kind"]))

    cone_rows = [r for r in rows if r[3]]
    cone_noncomment = [r for r in cone_rows if r[4] != "comment"]
    repo_noncomment = [r for r in rows if r[4] != "comment"]
    cone_token = len(cone_noncomment)           # 非 comment 口径（practices 对齐）
    repo_token_nc = len(repo_noncomment)
    cone_decl = len({r[2] for r in cone_noncomment})
    lp_token = sum(1 for r in repo_noncomment if r[0].startswith(LP_DIR_PREFIX))
    repo_files = len({r[0] for r in repo_noncomment})
    cone_files_with_sorry = len({r[0] for r in cone_noncomment})
    cone_by_dir = Counter()
    for rel, _ln, _d, _c, _k in cone_noncomment:
        parts = rel.split("/")
        cone_by_dir["/".join(parts[:2]) if rel.count("/") >= 2 else rel] += 1
    asm_rows = [r for r in cone_rows if r[0] == "Kepler/Assembly.lean"]
    asm_decl = len({r[2] for r in asm_rows if r[4] != "comment"})
    n_comment_repo = len(rows) - repo_token_nc
    n_comment_cone = len(cone_rows) - cone_token

    head = ""
    try:
        head = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                              cwd=args.repo, capture_output=True, text=True).stdout.strip()
    except OSError:
        pass

    print(f"repo={args.repo}  HEAD={head or 'unknown'}  "
          f"mode={'tracked-only' if args.tracked_only else 'fs-walk(含 untracked)'}")
    print(f"lean files scanned        : {len(files)}")
    print(f"repo-token (非 comment)   : {repo_token_nc}  in {repo_files} files  "
          f"(另有行注释 token {n_comment_repo}，不计入总数)")
    print(f"cone-token (Kepler.Final import closure, 非 comment) : {cone_token}  "
          f"in {cone_files_with_sorry} files  (closure size {len(cone_mods)} modules, "
          f"另有行注释 token {n_comment_cone})")
    for k in sorted(cone_by_dir):
        print(f"    cone breakdown {k:<28} {cone_by_dir[k]}")
    print(f"cone-decl (cone 声明级, 非 comment, 去重) : {cone_decl}  "
          f"(其中 Kepler/Assembly.lean: {asm_decl})")
    print(f"LP-debt ({LP_DIR_PREFIX})         : {lp_token}")
    kind_all = Counter(r[4] for r in rows)
    kind_cone = Counter(r[4] for r in cone_rows)
    print(f"kind repo : {dict(kind_all)}")
    print(f"kind cone : {dict(kind_cone)}")
    if parity_bad:
        print(f"PARITY WARN（removed vs masked 计数不一致，{len(parity_bad)} 文件）：")
        for rel, a, b in parity_bad[:20]:
            print(f"    {rel}: removed={a} masked={b}")
        print("    —— 总数以 removed（practices 口径）为准；TSV 行来自 masked。")

    rc = 0
    if args.check:
        print("--- check ---")
        fails = []
        # 仪器 SORRIED 段解析（--- SORRIED --- 到 --- AXIOMS --- 之间，第 2 列为全名）
        map_names: list[str] = []
        if os.path.isfile(map_tsv):
            in_sorried = False
            with open(map_tsv, "r", encoding="utf-8", errors="replace") as f:
                for line in f:
                    s = line.rstrip("\n")
                    if s == "--- SORRIED ---":
                        in_sorried = True
                        continue
                    if in_sorried and (s == "--- AXIOMS ---" or not s.strip()
                                       or s.startswith("---")):
                        break
                    if in_sorried and s.strip():
                        parts = s.split("\t")
                        if len(parts) >= 2:
                            map_names.append(parts[1])
        else:
            fails.append(f"找不到仪器文件 {map_tsv}")
        if repo_token_nc != args.expect_repo_token:
            fails.append(f"repo-token(非comment) {repo_token_nc} != 期望 "
                         f"{args.expect_repo_token}（practices-w1 逐文件复现口径；"
                         "差值需先查口径再改 pin，不许硬凑）")
        if cone_token != args.expect_cone_token:
            fails.append(f"cone-token(非comment) {cone_token} != 期望 "
                         f"{args.expect_cone_token}（Text 444 + Assembly 54 + Statement 1）")
        if lp_token != args.expect_lp_token:
            fails.append(f"LP-debt {lp_token} != 期望 {args.expect_lp_token}")
        if len(map_names) != EXPECT_MAP_SORRIED:
            print(f"NOTE: 仪器 SORRIED 行数 {len(map_names)} != 脚本记录的基线 "
                  f"{EXPECT_MAP_SORRIED}（仪器可能已重跑更新；对账仍按当前文件内容执行）")
        # 对账 1：仪器名单 ⊆ 静态 cone-decl ∪ 豁免（豁免 = 仪器 stale、当前树已证）
        cone_decl_names = {r[2] for r in cone_noncomment}
        missing = sorted({n for n in map_names if n not in cone_decl_names})
        unplanned = [n for n in missing if n not in EXEMPT_STALE_SORRIED]
        if unplanned:
            fails.append("仪器 SORRIED 中以下声明在静态 cone-decl 集合中找不到对应 "
                         f"sorry，且不在豁免清单：{unplanned}（豁免清单 = "
                         "EXEMPT_STALE_SORRIED，仅允许“仪器 stale、当前树已证”条目；"
                         "计划外缺失 = 声明被改名/删除或 census 解析缺陷，须查证）")
        # 对账 2：Assembly 静态债声明 ⊆ 仪器名单 ∪ 清单侧允许项
        asm_names = {r[2] for r in asm_rows if r[4] != "comment"}
        asm_extra = sorted(asm_names - set(map_names) - ASM_STATIC_EXTRA_ALLOW)
        if asm_extra:
            fails.append(f"Kepler/Assembly.lean 出现名单外的静态 sorry 声明：{asm_extra}"
                         "（新增声明级债；若确属清单侧同债形态，需有据修改 "
                         "ASM_STATIC_EXTRA_ALLOW 并入账）")
        asm_debt_now = len(set(map_names) & asm_names)
        print(f"map SORRIED={len(map_names)}（stale 基线 {EXPECT_MAP_SORRIED}）  "
              f"census: cone-decl={cone_decl}  asm-decl={asm_decl}  "
              f"asm∩map（当前仪器口径债）={asm_debt_now}  "
              f"stale-豁免={len(missing) - len(unplanned)}  "
              f"清单侧允许项={len(asm_names & ASM_STATIC_EXTRA_ALLOW)}")
        if parity_bad:
            fails.append("存在 removed/masked 计数 parity 不一致文件（见上），"
                         "TSV 与 token 总数可能不闭合")
        for f_ in fails:
            print(f"CHECK FAIL: {f_}")
        rc = 1 if fails else 0
        print(f"CHECK {'FAIL' if fails else 'PASS'}")

    if not args.no_tsv:
        out_path = args.out or os.path.join(args.repo, "docs", "sorry-census.tsv")
        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        with open(out_path, "w", encoding="utf-8") as f:
            f.write("file\tline\tdeclaration\tin_import_cone\tkind\n")
            for rel, ln, decl, in_cone, kind in sorted(rows):
                f.write(f"{rel}\t{ln}\t{decl}\t{1 if in_cone else 0}\t{kind}\n")
        print(f"wrote {out_path}  rows={len(rows)}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
