#!/usr/bin/env python3
"""P6-E work order: the 155-symbol definition closure of the 993 Flyspeck
nonlinear inequalities, cross-referenced with the Lean port status.

Reproduces the closure walk of kepler-g4e `pipeline/interval/parse_defs.py`
(steps 2-3 of its main(), walker at parse_defs.py:693):

  roots  = applied symbols / constants of out/ineqs_ast.json body_ast
           + domain_raw wrappers, minus the 15 statement variables;
  close transitively over out/defs.json bodies (defs.json already contains
           the fallback-extracted defs, so no HOL re-extraction is needed).

Reads (read-only; g4e modules are imported with bytecode writes disabled):
  kepler-g4e/pipeline/interval/out/ineqs_ast.json
  kepler-g4e/pipeline/interval/out/defs.json
  kepler-g4e/pipeline/interval/{parse_defs,parse_body}.py

Scans lean/Kepler/**/*.lean for the Lean-side status of each symbol:
  - B-convention anchors `/-- HOL `name` ...` followed by a def;
  - a plain `def <camelCase name>` (tier A);
  - stub bodies (`sorry`/`axiom`/`opaque` in the declaration block) -> tier C.

Lean status tiers:
  A = real body already in Lean (project-native / Mathlib for primitives)
  B = ported per convention B (camelCase rename + HOL anchor comment)
  C = stub (sorry/axiom/opaque placeholder)
  D = absent

Writes:
  docs/ineq-closure-155.md    human work-order table (one line per symbol)
  docs/ineq-closure-155.json  machine-readable version

Usage:  python3 lean/scripts/closure155.py [p6e_root]
        G4E=/path/to/kepler-g4e python3 lean/scripts/closure155.py
Exit code is nonzero if the reproduced closure stats drift from defs.json
__meta__ (87 roots / 155 closure / 124 resolved / 0 missing).
"""
import json
import os
import re
import sys

_args = [a for a in sys.argv[1:] if not a.startswith("--")]
ROOT = os.path.normpath(_args[0]) if _args else os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
G4E = os.environ.get(
    "G4E", os.path.join(os.path.dirname(ROOT), "kepler-g4e"))
G4E_INTERVAL = os.path.join(G4E, "pipeline", "interval")

sys.dont_write_bytecode = True          # g4e is read-only for us
sys.path.insert(0, G4E_INTERVAL)
import parse_body as pb                 # noqa: E402
import parse_defs as pd                 # noqa: E402

# ---------------------------------------------------------------- batch 1
# P6-E batch 1 (sqrtdelta rational family) + the enabler defs it needs
# (matan/lfun/rotateN were absent from Lean at batch-1 assignment time).
BATCH1 = {
    "dih_x_div_sqrtdelta_posbranch", "dih4_x_div_sqrtdelta_posbranch",
    "ldih_x_div_sqrtdelta_posbranch", "ldih2_x_div_sqrtdelta_posbranch",
    "ldih3_x_div_sqrtdelta_posbranch", "ldih5_x_div_sqrtdelta_posbranch",
    "ldih6_x_div_sqrtdelta_posbranch",
    "sol_euler_x_div_sqrtdelta", "sol_euler156_x_div_sqrtdelta",
    "sol_euler246_x_div_sqrtdelta", "sol_euler345_x_div_sqrtdelta",
    "delta4_squared_x",
}
BATCH1_ENABLERS = {
    "matan", "lfun", "rotate2", "rotate3", "rotate4", "rotate5", "rotate6",
}

# P6-E batch 2 (6-ary operator calculus, nonlin_def.hl) + enablers.
# rotate2-6 are nominally in batch 2's list but were already done in batch 1.
BATCH2 = {
    "proj_x2", "proj_x3", "proj_x5", "proj_x6",
    "proj_y4", "proj_y5", "proj_y6",
    "promote1_to_6", "promote3_to_6",
    "mk_126", "mk_135", "mk_456", "scalar6", "two6", "norm2hh",
}
BATCH2_ENABLERS = {"compose6", "constant6", "proj_x1", "proj_x4"}

# P6-E batch 3 (gamma/beta family) + enablers.  vol3f_456 was nominally a
# batch-5 member but is ported with batch 3 as a gamma3_x dependency.
BATCH3 = {
    "gamma2_x1_div_a_v2", "gamma3_x", "gamma3f_x_div_sqrtdelta",
    "gamma23_full8_x", "gamma23_keep135_x",
    "beta_bump_force_y", "beta_bump_lb",
}
BATCH3_ENABLERS = {
    "uni", "dummy6", "sol_x", "vol_x", "gamma2_x_div_azim_v2", "vol3f_456",
}

# P6-E batch 5 (misc).  matan was already done as a batch-1 enabler.
BATCH5 = {
    "tame_table_d", "dih2_y", "dih3_y", "lfun_y1", "rho_x", "ups_126",
    "dart_std3_big",
}
BATCH5_ENABLERS = {"dart_std3"}

# Per-symbol remarks (rendered in the md 备注 column).
NOTES = {
    "compose6": "defs.json body_ast 是截断的 parse 残片（{\"const\":\"f\"}），"
                "以 nonlin_def.hl:72-80 原文为准",
    "proj_x1": "HOL 多态；Lean 只移植闭包用到的 ℝ⁶→ℝ 实例",
    "proj_x2": "HOL 多态；同上",
    "proj_x3": "HOL 多态；同上",
    "proj_x4": "HOL 多态；同上",
    "proj_x5": "HOL 多态；同上",
    "proj_x6": "HOL 多态；同上",
    "norm2hh": "复用 PackingAuto2 的 hminus（Classical.epsilon 版）/hplus",
    "uni": "defs.json body_ast 截断（(f:A->B) 类型标注触发 parse bug）；"
           "HOL (f,x) 对在 Lean 解柯里化为 uni f x",
    "sol_x": "LocalAuto38:75 有 sorry 桩 solXP38（锚注释形式不同，扫描漏检）；"
             "批 3 在 IneqClosureDefs 立真体 solX",
    "vol_x": "PA20:99 volXf 为 verbatim 孪生，但 PA20 与 SphereKit 的 atn2 "
             "同名冲突使其不可跨 import 复用；批 3 立 canonical volX",
    "gamma2_x_div_azim_v2": "PA21:164 已有同名 verbatim 体；同上 atn2 冲突不"
             "可复用，批 3 立 canonical gamma2XDivAzimV2",
    "vol3f_456": "原批 5 名单，作为 gamma3_x 依赖随批 3 提前落地",
    "dart_std3": "define_dart 列表域（parse_defs triage unsupported）；"
                 "List (ℝ×ℝ×ℝ) 直接可移植，批 5 落地",
    "dart_std3_big": "= dart_std3 verbatim（ineq.hl:3079，'same domain but "
                     "extra disjunct'）",
    "tame_table_d": "ℕ 参数表常数；分支内 &r/&s 为 ℕ→ℝ cast，guard 在 ℕ 层",
    "matan": "批 5 名单，批 1 已作为 enabler 落地",
}

ANCHOR_RE = re.compile(r"/--\s*HOL\s*`([A-Za-z0-9_']+)`")
DEF_RE = re.compile(
    r"^(?:noncomputable\s+)?(def|theorem|lemma|axiom|opaque)\s+([A-Za-z0-9_']+)")
TOPLEVEL_RE = re.compile(
    r"^(?:noncomputable\s+)?(?:def|theorem|lemma|axiom|opaque|/--|/-!|"
    r"namespace|end|@\[)")


def camel(name):
    """B-convention rename: snake_case -> camelCase (delta_x -> deltaX)."""
    parts = name.split("_")
    return parts[0] + "".join(p.capitalize() for p in parts[1:])


# ------------------------------------------------------------ closure walk
def closure_roots():
    with open(os.path.join(G4E_INTERVAL, "out", "ineqs_ast.json")) as f:
        ast_data = json.load(f)
    roots = set()
    for rec in ast_data["records"]:
        a = rec.get("body_ast")
        bound = set()
        if isinstance(a, dict) and "forall" in a:
            bound = set(a["forall"].get("vars") or [])
        if a:
            pd.walk_syms(a, bound, roots)
        d = rec.get("domain_raw")
        if isinstance(d, str):
            where = rec.get("idv") or rec.get("idv_expr") or "<dom>"
            toks = pb.tokenize(d, where)
            if "//" in toks:
                toks, _ = pb.strip_slash_comments(toks, where)
                toks = pb.drop_dangling_disj(toks)
            pd.walk_syms(pb.strip_parens(pb.parse_tokens(toks, where)),
                         bound, roots)
    stmt_vars = {s for s in roots if pd.is_stmt_var(s)}
    return roots - stmt_vars, stmt_vars


def closure_walk(defs, roots):
    """Transitive closure of `roots` over defs.json bodies."""
    seen, work = set(), sorted(roots)
    while work:
        sym = work.pop()
        if sym in seen:
            continue
        seen.add(sym)
        if sym in pd.PRIMITIVES or sym not in defs:
            continue
        rec = defs[sym]
        ref = set()
        pd.walk_syms(rec["body_ast"], set(rec["params"]), ref)
        for s in sorted(ref - seen):
            if not pd.is_stmt_var(s):
                work.append(s)
    return seen


# ------------------------------------------------------------- lean survey
def survey_lean():
    """-> (anchors, defs) where
    anchors: hol_name -> (lean_name, file, line, stub)
    defs:    lean_name -> (file, line, stub)
    """
    anchors, defs = {}, {}
    lean_root = os.path.join(ROOT, "lean", "Kepler")
    for dirpath, _, files in os.walk(lean_root):
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, ROOT)
            with open(path) as f:
                lines = f.readlines()
            pending_anchor = None     # (hol_name, line_no)
            in_doc = False            # inside a `/-- ... -/` docstring
            for i, line in enumerate(lines):
                if in_doc:
                    if "-/" in line:
                        in_doc = False
                    continue
                m = ANCHOR_RE.search(line)
                if m:
                    pending_anchor = (m.group(1), i + 1)
                    if "-/" not in line:
                        in_doc = True
                    continue
                d = DEF_RE.match(line)
                if d:
                    kind, name = d.groups()
                    # crude block: until the next top-level declaration
                    block = [line]
                    for j in range(i + 1, min(i + 60, len(lines))):
                        if TOPLEVEL_RE.match(lines[j]):
                            break
                        block.append(lines[j])
                    stub = (kind in ("axiom", "opaque")
                            or re.search(r"\bsorry\b", "".join(block)))
                    defs.setdefault(name, (rel, i + 1, stub))
                    if pending_anchor and kind == "def":
                        anchors.setdefault(
                            pending_anchor[0], (name, rel, i + 1, stub))
                        pending_anchor = None
    return anchors, defs


# -------------------------------------------------------------------- main
def main():
    with open(os.path.join(G4E_INTERVAL, "out", "defs.json")) as f:
        data = json.load(f)
    meta = data["__meta__"]
    unsupported = data["__unsupported__"]
    defs = {k: v for k, v in data.items()
            if k not in ("__meta__", "__unsupported__")}

    roots, stmt_vars = closure_roots()
    seen = closure_walk(defs, roots)

    drift = []
    if len(roots) != meta["closure_roots"]:
        drift.append("roots %d != meta %d" % (len(roots),
                                              meta["closure_roots"]))
    if len(seen) != meta["closure_size"]:
        drift.append("closure %d != meta %d" % (len(seen),
                                                meta["closure_size"]))

    anchors, lean_defs = survey_lean()

    rows = []
    for sym in sorted(seen):
        if sym in pd.PRIMITIVES:
            cls, tier, lean = "primitive", "A", "Mathlib"
        elif sym in defs or sym in unsupported:
            cls = "resolved" if sym in defs else "unsupported"
            if sym in anchors:
                name, rel, line, stub = anchors[sym]
                tier = "C" if stub else "B"
                lean = "%s (%s:%d)" % (name, rel, line)
            elif camel(sym) in lean_defs:
                rel, line, stub = lean_defs[camel(sym)]
                tier = "C" if stub else "A"
                lean = "%s (%s:%d)" % (camel(sym), rel, line)
            else:
                tier, lean = "D", "-"
        elif sym in unsupported:
            cls, tier, lean = "unsupported", "D", "-"
        else:
            cls, tier, lean = "missing", "D", "-"
        batch = ("1" if sym in BATCH1
                 else "1(enabler)" if sym in BATCH1_ENABLERS
                 else "2" if sym in BATCH2
                 else "2(enabler)" if sym in BATCH2_ENABLERS
                 else "3" if sym in BATCH3
                 else "3(enabler)" if sym in BATCH3_ENABLERS
                 else "5" if sym in BATCH5
                 else "5(enabler)" if sym in BATCH5_ENABLERS else "")
        rows.append({"symbol": sym, "class": cls, "tier": tier,
                     "lean": lean, "batch": batch,
                     "note": NOTES.get(sym, ""),
                     "source": defs.get(sym, {}).get("source",
                                 unsupported.get(sym, {}).get("source", ""))})

    n_res = sum(1 for r in rows if r["class"] == "resolved")
    if n_res != meta["closure_resolved"]:
        drift.append("resolved %d != meta %d" % (n_res,
                                                 meta["closure_resolved"]))

    out_json = os.path.join(ROOT, "docs", "ineq-closure-155.json")
    out_md = os.path.join(ROOT, "docs", "ineq-closure-155.md")
    with open(out_json, "w") as f:
        json.dump({"meta": {"roots": len(roots), "closure": len(seen),
                            "resolved": n_res,
                            "statement_variables": sorted(stmt_vars),
                            "drift": drift},
                   "rows": rows}, f, indent=1, ensure_ascii=False)

    with open(out_md, "w") as f:
        f.write("""# P6-E: 155 定义闭包工单（ineqs_ast.json 根 → defs.json 传递闭包）

由 `lean/scripts/closure155.py` 生成（复现 kepler-g4e parse_defs.py 的
闭包游走；数据源只读）。每符号一行：

- class: resolved（defs.json 有体）/ primitive（内建实分析原语）/
  unsupported（parse_defs 无法解析的 HOL 体）/ missing（无定义）
- tier（Lean 侧现状）: A = 已有真体（项目原生/Mathlib）;
  B = 已按 B 档移植（camelCase + HOL 锚注释）; C = 桩（sorry/axiom）;
  D = 缺席
- batch: 批次号（1 = sqrtdelta 有理家族；2 = 6 元算子演算；
  N(enabler) = 批 N 依赖件）

| # | symbol | class | tier | Lean 侧 | batch | HOL source | 备注 |
|---|--------|-------|------|---------|-------|------------|------|
""")
        for i, r in enumerate(rows, 1):
            f.write("| %d | `%s` | %s | %s | %s | %s | %s | %s |\n"
                    % (i, r["symbol"], r["class"], r["tier"], r["lean"],
                       r["batch"], r["source"], r["note"]))
        f.write("\nclosure stats: roots=%d size=%d resolved=%d "
                "primitives=%d unsupported=%d missing=%d; "
                "statement variables excluded: %s\n"
                % (len(roots), len(seen), n_res,
                   sum(1 for r in rows if r["class"] == "primitive"),
                   sum(1 for r in rows if r["class"] == "unsupported"),
                   sum(1 for r in rows if r["class"] == "missing"),
                   ", ".join(sorted(stmt_vars))))
        tiers = {}
        for r in rows:
            if r["class"] == "resolved":
                tiers[r["tier"]] = tiers.get(r["tier"], 0) + 1
        f.write("resolved-by-tier: %s\n"
                % ", ".join("%s=%d" % kv for kv in sorted(tiers.items())))
        if drift:
            f.write("\n**DRIFT vs defs.json __meta__: %s**\n"
                    % "; ".join(drift))

    print("roots=%d closure=%d resolved=%d rows=%d"
          % (len(roots), len(seen), n_res, len(rows)))
    print("wrote %s" % out_md)
    print("wrote %s" % out_json)
    if drift:
        print("DRIFT: " + "; ".join(drift))
        return 1
    print("VALIDATION OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
