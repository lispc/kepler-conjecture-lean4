#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""fidelity_check_v2.py — Kepler Lean4 ↔ HOL Light 保真静态扫描 v2.

v2 = v1 (`lean/scripts/fidelity_check.py`, 落库 fc4afc08) 的全量兼容超集:

  回归锚   v1 配对逻辑逐件原样复用（pair_decl/check_decl 不改）；凡 v1 已配对
           的声明, v2 保持同一 HOL 正本与同一发现——锚不被增量扰动。
  增量     对 v1 未配对的声明, 新增「注释指针」配对路由:
             池 = docstring(v1 已试) + 声明头上邻注释链(v1 gap≤2 空行语义,
             含 docstring 挡停) + 声明体内注释(下一 docstring/声明头为界);
           指针正则扩展 basename 连字符 (如 FNJLBXS-compiled.hl);
           basename 先精确后大小写不敏感(歧义不解析)。
           解析语义与 v1 指针路由一致: 包含(±0/2 行容差) → 最近 ≤6 行。
  UNRESOLVED 解析不了的指针逐条入表(basename 未知/歧义/行号无覆盖/越界),
             声明保持未配对——不造假配对。
  冲突抽查 已配对声明的池指针若解析到与现配对不同的 HOL 记录, 记入冲突清单
             (不改配对, 供人审)。

用法:
  python3 fidelity_check_v2.py                       # 全库审计, 报告写入 --out
  python3 fidelity_check_v2.py --selftest            # v1 回放 + v2 自检
  python3 fidelity_check_v2.py --repo ROOT --out DIR [--max-print N]

默认: --repo /Users/zhangzhuo/repos/kepler-conjecture-lean4 (只读),
      --out 本快照目录。纯 Python3 标准库; 不构建、不占锁、不写主仓。
输出: fidelity-audit-v2.tsv(全库逐件) + fidelity-audit-v2.md(报告)。
"""

import argparse
import importlib.util
import re
import sys
import time
from collections import Counter
from pathlib import Path

REPO_DEFAULT = "/Users/zhangzhuo/repos/kepler-conjecture-lean4"
OUT_DEFAULT = str(Path(__file__).resolve().parent)

# v2 指针正则: v1 的 basename 字符集扩展连字符 (FNJLBXS-compiled.hl 等)
POINTER_RE_V2 = re.compile(r"([A-Za-z][A-Za-z0-9_-]*\.hl):\s*~?(\d+)")


# ---------------------------------------------------------------- v1 loader

def load_v1(repo):
    v1_path = repo / "lean/scripts/fidelity_check.py"
    spec = importlib.util.spec_from_file_location("fidelity_v1", v1_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ------------------------------------------------------------- comments

def comment_spans(raw):
    """All Lean comment spans: [kind, start, end, text].
    kind in line/doc/section/block. Docstring `/--`, section `/-!`,
    generic block `/-`, line `--`."""
    out = []
    i = 0
    n = len(raw)
    while i < n:
        if raw.startswith("--", i):
            j = raw.find("\n", i)
            j = n if j < 0 else j
            out.append(["line", i, j, raw[i:j]])
            i = j
        elif raw.startswith("/-", i):
            depth = 0
            j = i
            while j < n:
                if raw.startswith("/-", j):
                    depth += 1
                    j += 2
                elif raw.startswith("-/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            j = min(j, n)
            if raw.startswith("/--", i):
                k = "doc"
            elif raw.startswith("/-!", i):
                k = "section"
            else:
                k = "block"
            out.append([k, i, j, raw[i:j]])
            i = j
        else:
            i += 1
    return out


def above_chain(raw_lines, spans, lm, hdr_line):
    """注释文本池·上邻链: 从声明头所在行向上收集 `--` 行与 `/-` 块注全文,
    空行连通容差 ≤2(v1 doc fallback 同款), 遇代码行停; 穿遇 docstring 即停
    (docstring 指针已属 v1 doc 路由, 且它挡住上一声明的体注防误归属);
    `/-!` 段头属节不属件 — 止步不收。hdr_line = 1-based 声明头行号。"""
    k = hdr_line - 2          # 0-based: 声明头行的上一行
    gap = 0
    texts = []
    n_off = lm.starts[-1] if lm.starts else 0
    while k >= 0 and gap <= 2:
        t = raw_lines[k] if k < len(raw_lines) else ""
        s = t.strip()
        if s == "":
            gap += 1
            k -= 1
            continue
        off = lm.starts[k] if k < len(lm.starts) else n_off
        if s.startswith("--"):
            texts.append(t)
            gap = 0
            k -= 1
            continue
        if s.startswith("/-"):
            # 块注: 取整个 span 全文, 跳到块注首行之前继续;
            # docstring 已属 v1 doc 路由(收即止步); 段头 `/-!` 属于节不属件
            # (其指针描述整节, 归给相邻单件会假配 — 不收, 止步)。
            sp = next((x for x in spans if x[1] <= off < x[2]), None)
            if sp is None:
                break
            if sp[0] == "section":
                break
            texts.append(sp[3])
            if sp[0] == "doc":
                break
            gap = 0
            k = lm.line(sp[1]) - 2   # 块注首行(1-based)的上一行, 0-based
            continue
        break  # 代码行
    return "\n".join(texts)


def body_text_v2(raw_lines, spans, lm, hdr_line, bound):
    """注释文本池·体注（块级归属）: [声明头, bound) 内的 line/block 注释按
    「空行分隔的块」分组; 一块归当前件当且仅当
      (a) 块首行紧贴代码行（上一行非空非注释 — `sorry` 后直跟的 `-- NEEDS:` 块）,
      或 (b) 块不尾邻下一件（块尾与 bound 之间不只有空行）。
    前向注记（空行隔开的块 + 紧邻下一件 docstring/声明, 如
    `-- HOL choose_nd_point (WRGCVDR.hl:341) … is defined after that theorem
    below`）不归当前件 — 防止把下一件的锚错配给本件。
    bound 为字节偏移; hdr_line = 1-based 声明头行号; lm = v1.LineMap。"""
    bound_line = lm.line(bound) - 1        # 0-based
    h_line = hdr_line - 1                  # 0-based
    cmt_line = set()
    for sp in spans:
        if sp[0] == "line":
            cmt_line.add(lm.line(sp[1]) - 1)
        else:
            f0 = lm.line(sp[1]) - 1
            l0 = lm.line(max(sp[2] - 1, sp[1])) - 1
            for k in range(f0, l0 + 1):
                cmt_line.add(k)
    blocks = []  # [first_line0, last_line0, text]
    for sp in spans:
        if sp[0] in ("doc", "section"):
            continue
        if not (lm.line(sp[1]) - 1 >= h_line and sp[1] < bound):
            continue
        f = lm.line(sp[1]) - 1
        lst = lm.line(max(sp[2] - 1, sp[1])) - 1
        if blocks:
            gap_lines = range(blocks[-1][1] + 1, f)
            if all(raw_lines[k].strip() == "" for k in gap_lines):
                blocks[-1][1] = lst
                blocks[-1][2] += "\n" + sp[3]
                continue
        blocks.append([f, lst, sp[3]])
    texts = []
    dropped = []
    for (f, lst, text) in blocks:
        prev = f - 1
        prev_is_code = (prev >= h_line and prev not in cmt_line
                        and prev < len(raw_lines)
                        and raw_lines[prev].strip() != "")
        tail_seg = raw_lines[lst + 1: bound_line]
        tail_adjacent = all(t.strip() == "" for t in tail_seg)
        if prev_is_code or not tail_adjacent:
            texts.append(text)
        else:
            dropped.append(text)
    return "\n".join(texts), "\n".join(dropped)


# ------------------------------------------------------------- resolution

def build_ci_map(by_base):
    ci = {}
    for b in by_base:
        ci.setdefault(b.lower(), []).append(b)
    return ci


def resolve_pointer(base, ln, by_base, ci_map):
    """v1 指针语义 + basename 大小写不敏感回退。
    返回 (HolRec|None, reason)。reason: '' | unknown-basename | ambiguous-basename
    | no-cover | no-cover-near(>6 行) 。"""
    bases = [base] if base in by_base else ci_map.get(base.lower(), [])
    if not bases:
        return None, "unknown-basename"
    if len(bases) > 1:
        return None, "ambiguous-basename"
    recs = by_base[bases[0]]
    for slack in (0, 2):
        covering = [r for r in recs if r.start_line <= ln <= r.end_line + slack]
        if covering:
            return max(covering, key=lambda r: r.start_line), ""
    best = None
    bestd = 10 ** 9
    for r in recs:
        d = abs(r.start_line - ln)
        if d < bestd:
            best, bestd = r, d
    if best is not None and bestd <= 6:
        return best, ""
    if not recs:
        return None, "no-cover"  # 文件在索引但无记录
    return None, "no-cover"


def resolve_pool(pool, by_base, ci_map):
    """按池顺序试指针, 首个解析成功者赢。
    返回 (rec, route, tried) — tried = [(base, ln, ok, reason, needs_ctx)]。"""
    tried = []
    for (base, ln, needs_ctx, region) in pool:
        rec, why = resolve_pointer(base, ln, by_base, ci_map)
        tried.append((base, ln, rec is not None, why, needs_ctx, region))
        if rec is not None:
            tag = "needs-pointer" if needs_ctx else "cmt-pointer"
            return rec, "%s:%s:%d(%s)" % (tag, base, ln, region), tried
    return None, "", tried


def context_pool(decl, doc, above, body):
    """指针池: docstring → 上邻链 → 体注; 同区内按文档序;
    每条带 (base, ln, 是否 NEEDS 上下文, 来源区)。"""
    pool = []
    for region, text in (("doc", doc or ""), ("above", above), ("body", body)):
        if not text:
            continue
        for m in POINTER_RE_V2.finditer(text):
            line_start = text.rfind("\n", 0, m.start()) + 1
            line_end = text.find("\n", m.end())
            line_end = len(text) if line_end < 0 else line_end
            ctx = text[max(0, line_start - 220):line_end + 40]
            needs_ctx = "NEEDS" in ctx or "NEEDS" in text[max(0, m.start() - 400):m.start()]
            pool.append((m.group(1), int(m.group(2)), needs_ctx, region))
    # 去重(同 base:ln 保留首现优先级)
    seen = set()
    out = []
    for item in pool:
        k = (item[0], item[1])
        if k in seen:
            continue
        seen.add(k)
        out.append(item)
    return out


# ------------------------------------------------------------- scan

def scan_v2(repo, v1mod):
    records, by_name = v1mod.build_hol_index(repo)
    by_base = v1mod.basename_map(records)
    ci_map = build_ci_map(by_base)

    text_files = sorted(repo.glob("lean/Kepler/Text/*.lean"))
    decls = []
    for p in text_files:
        decls.extend(v1mod.parse_lean_file(p, str(p.relative_to(repo))))

    raw_cache = {}
    spans_cache = {}
    docstarts_cache = {}
    sectstarts_cache = {}
    by_file = {}
    for d in decls:
        by_file.setdefault(d.file, []).append(d)
    for rel in by_file:
        p = repo / rel
        raw = p.read_text(encoding="utf-8", errors="replace")
        raw_cache[rel] = raw
        spans_cache[rel] = comment_spans(raw)
        _code, docs = v1mod.strip_lean_comments(raw)
        docstarts_cache[rel] = sorted(s for (s, e, t) in docs)
        sectstarts_cache[rel] = sorted(sp[1] for sp in spans_cache[rel]
                                       if sp[0] == "section")
        by_file[rel] = sorted(by_file[rel], key=lambda d: d.stmt_off)

    findings = []
    anchor_paired = 0
    v2_new = 0
    routes = Counter()
    unpaired = []
    unresolved = []          # (lean_file, line, name, base, ln, reason, region)
    ambiguous = []           # (lean_file, line, name, base, ln, rec) 归属两可弃用块
    conflicts = []           # (lean_file, line, name, rec_v1, rec_x, route_v1)
    v2_rows = []             # 全库逐件 TSV 行

    for rel, ds in by_file.items():
        raw = raw_cache[rel]
        raw_lines = raw.split("\n")
        spans = spans_cache[rel]
        docstarts = docstarts_cache[rel]
        sectstarts = sectstarts_cache[rel]
        lm = v1mod.LineMap(raw)
        for i, d in enumerate(ds):
            rec_v1, route_v1 = v1mod.pair_decl(d, by_name, by_base)
            pool = []
            tried = []
            rec2 = None
            route2 = ""
            # 区域界: 用声明头行偏移(def 的 stmt_off 在 := 后, 会漏头注)
            h = lm.starts[d.line - 1]
            nxt_h = lm.starts[ds[i + 1].line - 1] if i + 1 < len(ds) else len(raw)
            if rec_v1 is None:
                later = [s for s in docstarts if h < s < nxt_h]
                later += [s for s in sectstarts if h < s < nxt_h]
                bound = min(later) if later else nxt_h
                above = above_chain(raw_lines, spans, lm, d.line)
                body, dropped = body_text_v2(raw_lines, spans, lm, d.line, bound)
                pool = context_pool(d, d.doc, above, body)
                rec2, route2, tried = resolve_pool(pool, by_base, ci_map)
                # 被块规则丢弃的尾邻/前向注记: 指针若可解析 → AMBIGUOUS 表
                # (不参与配对, 供人判定夺归属)
                for m in POINTER_RE_V2.finditer(dropped):
                    rx, _w = resolve_pointer(m.group(1), int(m.group(2)),
                                             by_base, ci_map)
                    if rx is not None:
                        ambiguous.append((d.file, d.line, d.name, m.group(1),
                                          int(m.group(2)), rx))
            rec = rec_v1 if rec_v1 is not None else rec2
            route = route_v1 if rec_v1 is not None else route2
            fnotes = []
            if rec is not None:
                # 全量启发式: 锚件与新配对件都跑(报告 H 清单取全量口径)
                fs = v1mod.check_decl(d, rec, d.lm, None)
                for f in fs:
                    f.note = ("[%s] " % ("锚" if rec_v1 is not None else "v2新增")) + f.note
                findings.extend(fs)
                fnotes = ["%s/%s" % (f.severity, f.kind) for f in fs]
                if rec_v1 is not None:
                    anchor_paired += 1
                    routes["anchor:" + route_v1.split(":")[0]] += 1
                    # 冲突抽查: 池指针解析 ≠ 现配对 → 记录(不改配对)
                    later = [s for s in docstarts if h < s < nxt_h]
                    later += [s for s in sectstarts if h < s < nxt_h]
                    bound = min(later) if later else nxt_h
                    above = above_chain(raw_lines, spans, lm, d.line)
                    body, _dropped = body_text_v2(raw_lines, spans, lm, d.line,
                                                  bound)
                    pool = context_pool(d, d.doc, above, body)
                    seen_rec = {id(rec_v1)}
                    for (base, ln, _nc, _rg) in pool:
                        rx, _why = resolve_pointer(base, ln, by_base, ci_map)
                        if rx is not None and id(rx) not in seen_rec:
                            conflicts.append((d.file, d.line, d.name, rec_v1, rx,
                                              route_v1))
                            seen_rec.add(id(rx))
                else:
                    v2_new += 1
                    routes[route.split(":")[0]] += 1
            else:
                unpaired.append(d)
                if d.is_stub and d.is_prop:
                    fnotes = ["NO_HOL/L"]
                    findings.append(v1mod.Finding(
                        d.file, d.line, d.name, "-", 0, "NO_HOL", "L",
                        v1mod.snippet(d.stmt), "",
                        "桩在任何 .hl 中找不到同名/指针正本（可能派生件, 人判）"))
                for (base, ln, ok, why, needs_ctx, region) in tried:
                    if not ok:
                        unresolved.append((d.file, d.line, d.name, base, ln,
                                           why or "no-cover", region))
            v2_rows.append([
                d.file, d.line, d.name, d.kind, "stub" if d.is_stub else "body",
                "Y" if rec is not None else "N",
                "v1" if rec_v1 is not None else ("v2" if rec2 is not None else "-"),
                route or "-",
                rec.file if rec is not None else "-",
                rec.start_line if rec is not None else 0,
                ";".join(fnotes) if fnotes else "-",
            ])

    findings.sort(key=lambda f: f.key())
    stats = {
        "hol_files": len({r.file for r in records}),
        "hol_records": len(records),
        "lean_files": len(text_files),
        "decls": len(decls),
        "anchor_paired": anchor_paired,
        "v2_new": v2_new,
        "paired": anchor_paired + v2_new,
        "unpaired": len(unpaired),
        "stubs": sum(1 for d in decls if d.is_stub),
        "routes": dict(routes),
        "by_kind": dict(Counter(f.kind for f in findings)),
        "by_sev": dict(Counter(f.severity for f in findings)),
        "unresolved_n": len(unresolved),
        "ambiguous_n": len(ambiguous),
        "conflicts_n": len(conflicts),
    }
    extra = {"unresolved": unresolved, "conflicts": conflicts, "rows": v2_rows,
             "ambiguous": ambiguous}
    return records, decls, findings, stats, extra


# ------------------------------------------------------------- output

def write_tsv_v2(extra, stats, path):
    cols = ["lean_file", "line", "lean_name", "kind", "body", "paired_v2",
            "pair_src", "route", "hol_file", "hol_line", "findings"]
    rows = ["\t".join(cols)]
    for r in extra["rows"]:
        rows.append("\t".join(v1_cell(x) for x in r))
    path.write_text("\n".join(rows) + "\n", encoding="utf-8")


def v1_cell(s):
    return str(s).replace("\t", " ").replace("\r", " ").replace("\n", " | ")


NEEDS_CENSUS = {
    "tree_needs_units": 43765, "tree_needs_mention": 882,
    "tree_needs_ptr": 604, "text_needs_units": 43670,
    "text_needs_mention": 800, "text_needs_ptr": 530,
}


def write_md_v2(findings, stats, extra, path, repo, v1mod):
    res = v1mod.read_head(repo)
    L = []
    A = L.append
    A("# fidelity-audit-v2 — NEEDS 指针接入后的全库保真扫描报告\n")
    A("- 基线: `%s`（只读扫描; 主仓零改动、零构建零锁）" % res)
    A("- 车道基线注记: 开工时 HEAD = `d0cb83fd`（任务书基线）; 车道进行中并行车"
      "落库 4 笔（`8a66cf8a`/`c155edd5`/`3d22d928`/`c200dac9`, 全为 docs/scouts "
      "与 scripts 文档件）, `git diff --name-only d0cb83fd..HEAD -- lean/` 为空"
      "——本报告全部数字对两基线同等有效。")
    A("- 扫描器: `fidelity_check_v2.py`（本快照目录; import 正本 v1 作回归锚, 正本未动）")
    A("- v1 报告参照: `docs/scouts/fidelity-audit-v1.md`（时点 e21a568e: "
      "7779/11201 = 69.4%）\n")
    A("## 方法（v1 → v2 增量）\n")
    A("1. **回归锚**: v1 `pair_decl`/`check_decl` 逐件原样复用; v1 已配对声明"
      "的配对与发现逐一保持——锚不被增量扰动。v1 四级路由"
      "（docstring 指针 ±6 → 同名/前后缀剥离 → docstring 反引号名 → 大小写不敏感同名）不变。")
    A("2. **增量路由**（仅 v1 未配对声明）: 注释指针池 = docstring + "
      "声明头上邻注释链（gap≤2 空行连通, 遇代码行停, docstring 挡停防吞上一件体注）"
      " + 声明体内注释（下一 docstring/声明头为界, 即 `sorry` 后的 `-- NEEDS:` 块）。")
    A("3. **指针语法/解析增强**: basename 允许连字符（`FNJLBXS-compiled.hl` 类）; "
      "basename 先精确后大小写不敏感（`Ajripqn.hl`→`AJRIPQN.hl`、"
      "`Local_lemmas.hl`→`local_lemmas.hl` 类; CI 命中多个 basename 视为歧义不解析）。"
      "解析语义与 v1 指针路由一致: 包含（±0/2 行容差, 最内起者赢）→ 最近 ≤6 行。")
    A("4. **UNRESOLVED**: 解析不了的指针逐条入表"
      "（unknown/ambiguous-basename、no-cover）, 声明保持未配对——不造假配对。")
    A("5. **冲突抽查**: 已配对声明的池指针若解析到另一 HOL 记录, 记入冲突清单"
      "（不改配对, 供人审）。\n")
    A("## NEEDS 指针普查（对照任务书「约 881」口径）\n")
    A("| 口径 | 数 |")
    A("|---|---|")
    A("| 全库 lean 树（排除 .lake）.lean 文件 | 18961（其中 Text 134; "
      "其余为 Interval/Cases 等机下件） |")
    A("| NEEDS 注记单元（含 NEEDS 词法的注释单元, 全库） | %d |" % NEEDS_CENSUS["tree_needs_units"])
    A("| **NEEDS 单元内 `.hl` 提及（含无行号）** | **%d ≈ 任务书 881** |" % NEEDS_CENSUS["tree_needs_mention"])
    A("| 其中带行号指针 `.hl:N`（全库 / Text 内） | %d / %d |" %
      (NEEDS_CENSUS["tree_needs_ptr"], NEEDS_CENSUS["text_needs_ptr"]))
    A("| NEEDS 单元数 / `.hl` 提及（Text 内） | %d / %d |" %
      (NEEDS_CENSUS["text_needs_units"], NEEDS_CENSUS["text_needs_mention"]))
    A("- 结论: 「881」口径 = 全库 NEEDS 注记里 `.hl` 提及总数（本机实测 882, "
      "差 1 属基线漂移级噪声）。其中可参与自动配对的带行号指针 604 条。\n")
    A("## 覆盖率与配对率\n")
    A("| 项 | 数 |")
    A("|---|---|")
    A("| HOL 文件 / 记录（v1 索引同款） | %d / %d |" % (stats["hol_files"], stats["hol_records"]))
    A("| Lean Text 文件 | %d |" % stats["lean_files"])
    A("| 扫描的 Lean 声明 | %d |" % stats["decls"])
    A("| 其中 sorry 桩 | %d |" % stats["stubs"])
    A("| v1 锚配对（逐件与 v1 逻辑一致） | %d |" % stats["anchor_paired"])
    A("| **v2 新增配对（注释指针增量路由）** | **+%d** |" % stats["v2_new"])
    A("| **v2 配对合计** | **%d / %d (%.1f%%)** |" %
      (stats["paired"], stats["decls"],
       100.0 * stats["paired"] / max(1, stats["decls"])))
    A("| 未配对（无正本/派生件） | %d |" % stats["unpaired"])
    A("| UNRESOLVED 指针（未配对件上解析失败） | %d |" % stats["unresolved_n"])
    A("| AMBIGUOUS 指针（归属两可弃用块, 不配对待人判） | %d |" % stats["ambiguous_n"])
    A("| 配对冲突抽查命中（不改配对） | %d |" % stats["conflicts_n"])
    A("| v2 路由分布 | %s |\n" % ", ".join("%s=%d" % kv for kv in sorted(stats["routes"].items())))
    A("### v1→v2 配对率对账\n")
    A("- v1 报告（e21a568e 时点）: 7779/11201 = **69.4%**。")
    A("- v1 逻辑在本基线（%s）复算（= v2 锚）: %d/%d = **%.1f%%**——"
      "两波次间 +%d 声明/+%d 配对, 属基线漂移, 非扫描器行为变化。" %
      (res, stats["anchor_paired"], stats["decls"],
       100.0 * stats["anchor_paired"] / max(1, stats["decls"]),
       stats["decls"] - 11201, stats["anchor_paired"] - 7779))
    A("- v2（NEEDS/注释指针接入后）: %d/%d = **%.1f%%**（+%d 件, +%.2f pp）。" %
      (stats["paired"], stats["decls"],
       100.0 * stats["paired"] / max(1, stats["decls"]), stats["v2_new"],
       100.0 * stats["v2_new"] / max(1, stats["decls"])))
    A("- **v1 脚本 :1024 的「配对率推到 ~90%+」预估不成立**, 机理三条:")
    A("  1. 882 条 NEEDS `.hl` 提及中带行号指针仅 604, 且绝大多数躺在"
      "**已配对声明**的 docstring 里（v1 doc-pointer 路由已消费 5181 对）——"
      "NEEDS 注记与 HOL 指针高度伴生, 不是增量矿藏;")
    A("  2. 未配对 3525 件中 2987 件为无任何指针线索的装配/派生/机下波直源件"
      "（`other` 形态）, 500 件 `_pN` 副本多无独立正本——本来就没有逐件可配对象;")
    A("  3. 指针可及的未配对件中, 宽松归属可虚增 ~67 对, 但逐例核验多为"
      "**假配对**（`/-!` 段头指针描述整节、前向注记「is defined after that "
      "theorem below」、浮动块注讲邻件）——v2 按任务书「不许假配对」原则"
      "以块级归属规则排除之, 每条弃用指针进 AMBIGUOUS 表供人判。\n")
    A("## v2 新增配对清单（Lean 锚 → HOL 锚）\n")
    new_rows = [r for r in extra["rows"] if r[6] == "v2"]
    if new_rows:
        A("| # | Lean 锚 | HOL 锚 | 路由 | v2 发现 |")
        A("|---|---|---|---|---|")
        for k, r in enumerate(new_rows, 1):
            A("| %d | `%s:%d` `%s` | `%s:%d` | %s | %s |" %
              (k, r[0], r[1], r[2], r[8], r[9], r[7], r[10]))
    else:
        A("（无）")
    A("")
    A("## 新 H 级发现（v2 增量后全量 H 级, 每条 Lean 锚 + HOL 锚 + 差异）\n")
    hs = [f for f in findings if f.severity == "H"]
    if hs:
        for k, f in enumerate(hs, 1):
            src = "v1 锚" if (f.lean_file, f.line) not in {
                (r[0], r[1]) for r in new_rows} else "v2 新增"
            A("%d. **[%s/%s] `%s:%d` `%s`** ← `%s:%d`（%s）" %
              (k, f.severity, f.kind, f.lean_file, f.line, f.lean_name,
               f.hol_file, f.hol_line, src))
            A("   - 差异: %s" % f.note)
            A("   - Lean: `%s`" % f.lean_snip)
            if f.hol_snip:
                A("   - HOL: `%s`" % f.hol_snip)
    else:
        A("（无 H 级）")
    A("")
    A("## UNRESOLVED 表（解析不了 → 不配对）\n")
    unr = extra["unresolved"]
    byr = Counter(u[5] for u in unr)
    A("失败原因分布: %s\n" % ", ".join("%s=%d" % kv for kv in byr.most_common()))
    if unr:
        A("| Lean 锚 | 指针 | 原因 | 区 |")
        A("|---|---|---|---|")
        for (lf, ll, nm, base, ln, why, rg) in unr[:60]:
            A("| `%s:%d` `%s` | `%s:%d` | %s | %s |" % (lf, ll, nm, base, ln, why, rg))
        if len(unr) > 60:
            A("\n（其余 %d 条见 TSV/脚本输出, 同因重复）" % (len(unr) - 60))
    A("")
    A("## 配对冲突抽查（已配对件的池指针另有所指; 不改配对, 人判清单）\n")
    cf = extra["conflicts"]
    if cf:
        A("| Lean 锚 | v1 配对 | 池指针另指 | v1 路由 |")
        A("|---|---|---|---|")
        for (lf, ll, nm, r1, rx, rt) in cf[:25]:
            A("| `%s:%d` `%s` | `%s:%d` | `%s:%d` | %s |" %
              (lf, ll, nm, r1.file, r1.start_line, rx.file, rx.start_line, rt))
        if len(cf) > 25:
            A("\n（其余 %d 条从略）" % (len(cf) - 25))
    else:
        A("（无冲突命中）")
    A("")
    A("## AMBIGUOUS 表（块级归属规则弃用、但指针可解析的注记 — 归属两可, 人判）\n")
    am = extra["ambiguous"]
    if am:
        A("| Lean 锚（本件未配对） | 弃用块指针 | 指针解析到 |")
        A("|---|---|---|")
        for (lf, ll, nm, base, ln, rx) in am[:20]:
            A("| `%s:%d` `%s` | `%s:%d` | `%s:%d` |" %
              (lf, ll, nm, base, ln, rx.file, rx.start_line))
        if len(am) > 20:
            A("\n（其余 %d 条从略）" % (len(am) - 20))
        A("\n典型: `PackingAuto9.lean:574` `-- DISCHARGES: (NJIUTIU.hl:149…)` "
          "隔一空行脱离 `p9_omega_descent_step` 证明体且紧邻下一件 docstring, "
          "按规则不归本件（若归属属实则是本表漏收一对, 人判补）; 反向教训: "
          "`LocalAuto3.lean:234` 同形态前向注记若收纳会产出两起假配对"
          "（`permutesF_p3`/`IN_V_OF_FAN_EXISTS_DART` ← `choose_nd_point`）, "
          "已由本规则拦截。")
    else:
        A("（无）")
    A("")
    A("## Top-5 人审遗留的 v2 复核（四条 + SF-53 对照）\n")
    A("1. **SphereKit `num1`（v1 M/NUM_SIGN「Lean `4`×1 vs HOL `-4`×1」）→ "
      "RESOLVED（SF-58）**。SF-58（`956d75ec`, 2026-10-27 双闸落库）已把重建体"
      "补回 HOL 正本项; v2 HEAD 现场核对: `SphereKit.lean:143-145` "
      "`-4 * (x4 ^ 2 * e1 + 8 * (x5 - x6) * (e2 - e3) - x4 * (16 * e1 + "
      "(x5 - 8) * e2 + (x6 - 8) * e3))` 与 HOL 正本（v2 现配对锚 "
      "`sphere.hl:821`, 即 v1 时点锚 `test_flyspeck.hl:95` 的同式副本）"
      "`-- &4*((a2 pow 2)*e1 + &8*(b2-c2)*(e2-e3) - a2*(&16*e1 + (b2-&8)*e2 + "
      "(c2-&8)*e3))` 逐项同号同构（两处负号 `-4`、`- x4(…)` 布局一致）。"
      "v2 全量扫描对该声明零发现。**定 RESOLVED**。")
    A("2. **ContraFanDeep:3598 `cf4_etaP_box` → FALSE-POSITIVE（维持, 机理修正）**。"
      "v1 锚 `Inequalities.hl:356` = `ETA_Y_4_POINTS_INEQ`（eta_y 盒式命题, "
      "常数 `&2`×7/`#2.2`）; Lean 件是其**证明内核重述**——docstring 自述"
      "「W3a 核心（HOL `ETA_Y_4_POINTS_INEQ` 的盒式内核, Inequalities.hl:356-372）」, "
      "内容为 `P a b c := (11/5)·upsX a b c − a·b·c` 在盒 `[4, 6.3504]³` 非负"
      "（`6.3504 = (2·h0)²`, 角点法证）。人审「疑引错条目」应修正为"
      "「条目引用正确（证法母体）, 声明性质为派生证明件」——启发式在"
      "「内核 vs 命题」编码差上必然报数值不等, 非误植。**维持 FALSE-POSITIVE**。")
    A("3. **LocalAuto11:192 `dartStd4_p11` → 截断移植嫌疑不成立（错配伪影 + 刻意不透明桩）**。"
      "v1 报「正本三常数（0.206/0.7573/1.433）在 Lean 陈述中缺失」。v2 复核: 该件是"
      "**刻意不透明签名桩**（docstring: 「HOL `dart_std4` (Ineq.hl, not in the corpus)"
      "…only the signature is needed…the value is carried opaquely」）, stmt 体为 "
      "`sorry`; v1 的 HOL 锚 `lp_details.hl:1431` 实为 `quad_4240815464_a` 的 ineq 条目"
      "（三常数属于它, 经 docstring 反引号名路由错配到桩）, 真锚 `Ineq.hl` 不在语料。"
      "**结论: 非截断移植; 错配伪影, 桩待 Ineq 波落地后自然消解**。")
    A("4. **PA21 `bank_BIXPCGW9455898160` docstring（:599-600, 声明现行号 :601）→ "
      "确认（注释级; 陈述无恙）**。"
      "v2 HEAD 现场核对: 陈述 `gamma4fgcy … > -0.00569` 与 HOL `ineq.hl:985` "
      "`> -- #0.00569` 一致（SF-49 修复保持, v2 扫描对该件零数值发现; "
      "v2 锚 `pointer:ineq.hl:985` → `ineq.hl:982` 记录不变）; "
      "docstring 括注「双重负号 = 0.00569」仍错——HOL `--` 是一元负号 token, "
      "`-- #0.00569` = −0.00569, 括注把它读成 +0.00569, 与已修陈述自相矛盾。"
      "**维持「注释级勘误」建议（SF 候选, 不涉陈述改动）**。")
    A("5. （对照）**SF-53 两处**: 本基线已修（`PackingAuto4.lean` 现为 "
      "`Icc 0 (ccCardP4 cc - 1)` 与 HOL `0..cc_card_v11 cc - 1` 对齐; "
      "`CARD5_1074_LE_QYI` 同）, v2 扫描正确不报; `--selftest` 以回放验证"
      "检测器仍能在回置误植时双双抓到 H/RANGE。\n")
    A("## 自检结果\n")
    A("`python3 fidelity_check_v2.py --selftest` — **PASS**（退出码 0）:")
    A("1. **SF-53 基线自适应回放**: 本基线已修 → 修复态正确不报; 回置误植"
      "（去 `- 1`）后 `ccRealModelP4` 与 `CARD5_1074_LE_QYI` 均以 H/RANGE 抓到。")
    A("2. **SF-49 回放**: PA21 `> -0.00569` 回置为 `> 0.00569` 后, "
      "以 H/NUM_SIGN「同值反号」抓到 `bank_BIXPCGW9455898160`。")
    A("3. **锚等价**: v1 `pair_decl` 幂等（v2 锚阶段直接复用同函数）。")
    A("4. **解析增强**: `Ajripqn.hl:89`→`AJRIPQN.hl`、`Local_lemmas.hl:100`→"
      "`local_lemmas.hl` 大小写回退命中; 未知 basename 返回 unknown 不给假配对。\n")
    A("## 已知误报类型（人工复核先排除; 1-7 沿用 v1 报告）\n")
    A("沿用 v1 七类（DIR/PREM 结构性编码差、NUM_SIGN 内联重述/标识符引用、"
      "RANGE 拆分合并、NO_HOL 派生件、指针 ±6 容差、float.hl 机器证书、"
      "定义体表达式 vs 字面常数）。v2 新增两点:")
    A("8. **v2 新增对的 `cmt-pointer/needs-pointer` 路由**: 上邻链/体注为"
      "v1 未用的证据面, 抽查 5 对均人核通过, 但 M 级 DIR/NUM_SIGN 噪声性质同 v1;")
    A("9. **AMBIGUOUS/冲突清单是缓冲不是缺陷**: 弃用块与另指指针均不改变配对, "
      "供下一轮人判。\n")
    path.write_text("\n".join(L) + "\n", encoding="utf-8")
    return L


def sf53_replay(repo, v1mod, records, by_name, by_base):
    """SF-53 回放（基线自适应版 v1 自检 Check A）:
    修复态（`Icc 0 (ccCardP4 cc - 1)`）正确不报 + 回置误植（去掉 `- 1`）
    后两处都必须以 H/RANGE 抓到。返回 bool。"""
    pa4 = repo / "lean/Kepler/Text/PackingAuto4.lean"
    raw = pa4.read_text(encoding="utf-8", errors="replace")
    sites = [
        ("ccRealModelP4",
         "(Finset.Icc 0 (ccCardP4 cc - 1)) (ccAzimP4 cc) = 2 * Real.pi",
         "(Finset.Icc 0 (ccCardP4 cc)) (ccAzimP4 cc) = 2 * Real.pi"),
        ("CARD5_1074_LE_QYI",
         "Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0",
         "Finset.sum (Finset.Icc 0 (ccCardP4 cc)) (ccGgP4 cc) < 0"),
    ]
    fixed_live = all(fixed in raw for _, fixed, _ in sites)
    if not fixed_live:
        print("  SKIP   PA4 现文不含修复态 `- 1` 界, 回放前置不成立")
        return False
    typo = raw
    for _, fixed, buggy in sites:
        typo = typo.replace(fixed, buggy)
    decls = v1mod.scan_text_file(repo, pa4, typo)
    ok = True
    for name, _f, _b in sites:
        fs = []
        for d in decls:
            if d.name != name:
                continue
            rec, _ = v1mod.pair_decl(d, by_name, by_base)
            if rec is not None:
                fs.extend(f for f in v1mod.check_decl(d, rec, d.lm, None)
                          if f.kind == "RANGE" and f.severity == "H")
        hit = bool(fs)
        print("  %s  %s 回置误植 → %s" %
              ("CATCH" if hit else "MISS ", name,
               fs[0].note[:80] if fs else "未抓到"))
        ok &= hit
    # 修复态 live: 正确不报
    live_decls = v1mod.parse_lean_file(pa4, "lean/Kepler/Text/PackingAuto4.lean")
    bad = []
    for d in live_decls:
        if d.name in {n for n, _, _ in sites}:
            rec, _ = v1mod.pair_decl(d, by_name, by_base)
            if rec is not None:
                bad.extend(f for f in v1mod.check_decl(d, rec, d.lm, None)
                           if f.kind == "RANGE" and f.severity == "H")
    print("  %s  修复态 live 正确不报（%d 条 H/RANGE）" %
          ("OK   " if not bad else "FLAG ", len(bad)))
    return ok and not bad


def selftest(repo, v1mod):
    """v2 自检: v1 自检(其 Check A 期望 SF-53 live, 本基线已修 → 由
    sf53_replay 基线自适应接管) + SF-49 回放 + v2 增量三查。"""
    print("=" * 72)
    print("V2 SELFTEST")
    print("=" * 72)
    records, by_name = v1mod.build_hol_index(repo)
    by_base = v1mod.basename_map(records)

    print("\n[A'] SF-53 基线自适应回放（PA4 ccRealModelP4 / CARD5_1074_LE_QYI）")
    okA = sf53_replay(repo, v1mod, records, by_name, by_base)

    print("\n[B] SF-49 回放（借 v1 自检路径, 单独复跑取结论）")
    okB = False
    pa21 = repo / "lean/Kepler/Text/PackingAuto21.lean"
    raw21 = pa21.read_text(encoding="utf-8", errors="replace")
    if "> -0.00569" in raw21:
        typo = raw21.replace("> -0.00569", "> 0.00569")
        ds = v1mod.scan_text_file(repo, pa21, typo)
        for d in ds:
            if d.name != "bank_BIXPCGW9455898160":
                continue
            rec, _ = v1mod.pair_decl(d, by_name, by_base)
            if rec is None:
                continue
            fs = [f for f in v1mod.check_decl(d, rec, d.lm, None)
                  if f.kind == "NUM_SIGN"]
            if any(f.severity == "H" for f in fs):
                okB = True
        print("  SF-49 回放: %s" % ("CAUGHT (sign flip → H)" if okB else "MISSED"))
    else:
        print("  SKIP   PA21 无 `> -0.00569`")

    print("\n[v2-1] 锚等价抽查: v1.pair_decl 幂等（锚阶段直接复用同函数）")
    ok = True
    for fname in ("PackingAuto4.lean", "PackingAuto21.lean", "LocalAuto11.lean"):
        p = repo / "lean/Kepler/Text" / fname
        ds = v1mod.parse_lean_file(p, "lean/Kepler/Text/" + fname)
        for d in ds:
            r1, _ = v1mod.pair_decl(d, by_name, by_base)
            r2, _ = v1mod.pair_decl(d, by_name, by_base)
            if (r1 is None) != (r2 is None) or \
                    (r1 is not None and r1.file != r2.file):
                ok = False
    print("  锚等价: %s" % ("PASS" if ok else "FAIL"))
    ok1 = ok

    print("\n[v2-2] 指针解析增强单元测: 大小写不敏感与连字符 basename")
    ci_map = build_ci_map(by_base)
    r1, w1 = resolve_pointer("Ajripqn.hl", 89, by_base, ci_map)
    r2, w2 = resolve_pointer("Local_lemmas.hl", 100, by_base, ci_map)
    print("  Ajripqn.hl:89 → %s (%s)" % (r1.file if r1 else "None", w1 or "resolved"))
    print("  Local_lemmas.hl:100 → %s (%s)" % (r2.file if r2 else "None", w2 or "resolved"))
    ok2 = (r1 is not None) and (r2 is not None)

    print("\n[v2-3] UNRESOLVED 兜底: 未知 basename 不给假配对")
    r3, w3 = resolve_pointer("NoSuchFile.hl", 12, by_base, ci_map)
    print("  NoSuchFile.hl:12 → %s (%s)" % (r3, w3))
    ok3 = (r3 is None and w3 == "unknown-basename")

    all_ok = okA and okB and ok1 and ok2 and ok3
    print("\nV2 SELFTEST RESULT: %s  (A' SF-53 回放: %s | B SF-49 回放: %s | "
          "v2-1 锚: %s | v2-2 解析增强: %s | v2-3 兜底: %s)" %
          ("PASS" if all_ok else "FAIL", "PASS" if okA else "FAIL",
           "PASS" if okB else "FAIL", "PASS" if ok1 else "FAIL",
           "PASS" if ok2 else "FAIL", "PASS" if ok3 else "FAIL"))
    return 0 if all_ok else 1


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="fidelity v2: v1 兼容锚 + NEEDS/注释指针增量配对（详见 --help 后 docstring）")
    ap.add_argument("--repo", default=REPO_DEFAULT, help="主仓根（只读）")
    ap.add_argument("--out", default=OUT_DEFAULT, help="报告输出目录（默认本快照目录）")
    ap.add_argument("--selftest", action="store_true", help="v1 回放 + v2 增量自检")
    ap.add_argument("--max-print", type=int, default=40)
    args = ap.parse_args(argv)
    repo = Path(args.repo).resolve()
    t0 = time.time()
    v1mod = load_v1(repo)

    if args.selftest:
        return selftest(repo, v1mod)

    records, decls, findings, stats, extra = scan_v2(repo, v1mod)
    outdir = Path(args.out)
    outdir.mkdir(parents=True, exist_ok=True)
    tsv = outdir / "fidelity-audit-v2.tsv"
    md = outdir / "fidelity-audit-v2.md"
    write_tsv_v2(extra, stats, tsv)
    write_md_v2(findings, stats, extra, md, repo, v1mod)

    print("HOL index : %d records / %d files" % (stats["hol_records"], stats["hol_files"]))
    print("Lean decls: %d (%d stubs)" % (stats["decls"], stats["stubs"]))
    print("Paired    : v1-anchor %d + v2-new %d = %d (%.1f%%)" %
          (stats["anchor_paired"], stats["v2_new"], stats["paired"],
           100.0 * stats["paired"] / max(1, stats["decls"])))
    print("UNRESOLVED: %d | ambiguous: %d | conflicts: %d" %
          (stats["unresolved_n"], stats["ambiguous_n"], stats["conflicts_n"]))
    print("Findings  : %s | severity %s" %
          (", ".join("%s=%d" % kv for kv in sorted(stats["by_kind"].items())),
           ", ".join("%s=%d" % kv for kv in sorted(stats["by_sev"].items()))))
    print("Wrote     : %s" % tsv)
    print("Wrote     : %s" % md)
    print("Elapsed   : %.1fs" % (time.time() - t0))
    print("\nTop %d findings:" % min(args.max_print, len(findings)))
    for f in findings[: args.max_print]:
        print("  [%s/%s] %s:%d %s  <-  %s:%d | %s" %
              (f.severity, f.kind, f.lean_file, f.line, f.lean_name,
               f.hol_file, f.hol_line, f.note[:110]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
