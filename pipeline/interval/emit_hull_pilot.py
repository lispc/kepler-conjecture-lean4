#!/usr/bin/env python3
"""549 schema-v3 hull route — 200-leaf kernel-verification launch drill.

Scales the 20-leaf `C549HullPilot` to 200 sampled tm-hit leaves to measure
launch throughput (emit + kernel build) for the full 281,894-leaf emission.
Reuses the emit_lean.py `--hull` machinery (hull_expr / hull_stage_a_file /
parse_hull_params; evalTMHullD / checkPosTMHull semantics, guard-first
certificate order) and the probe_l1.py mmap byte-offset sampling.

Subcommands:
  sample <cert.json> <out_boxes.json> <out_manifest.json> [--k=200]
      Stride-sample k hit=="tm" cert leaves via mmap leaf-start offsets
      (no full JSON parse; one bounded raw_decode per pick).  Writes a
      bb_arb --probe-compatible boxes file plus a manifest (stride, picked
      cert leaf indices, sampling provenance).
  stagea <case.json> <boxes.json> <out_driver.lean>
         [--rung=N --rung-out=E --gran=G]
      Emit the compiled-run probe driver (emit_lean --hull stage-A shape:
      `tmHullLeafProbe` per leaf; prints the RUNG header then per-leaf
      `<i> PASS|NEG <lo_m> <lo_e> <slo shi sc>...` lines).  Run with
      `lake env lean --run` from the `lean/` package root.
   stageb <case.json> <boxes.json> <params.txt> <hullstats.jsonl> <out.lean>
          [--shard=50] [--tactic=decide|native_decide]
       Emit the kernel pilot file: per-leaf
       `checkPosTMHull <mod>Expr <mod>BoxK <mod>P<K> = true|false` decide
       theorems grouped into `--shard`-leaf shard sections (conjunction
       theorems referencing the leaf theorems — no recomputation), a summary
       conjunction over the shards, and `#print axioms`.  `--tactic` picks
       the leaf proof vehicle: `decide` (default, pure kernel, ~21.4 s/leaf)
       or `native_decide` (Lean compiler+runtime enters the TCB; one scoped
       `Lean.ofReduceBool`-shaped axiom per leaf — the DECISIONS.md
       2026-08-10/2026-09-19 scoped exceptions do NOT yet cover
       `Kepler.Interval.Cases.C549Hull*`, so production use needs its own
       DECISIONS.md entry + human sign-off).  Joins the C-side
       `bb_arb --probe --hull-stats` single/straddle classification per box
       for the known-criteria PASS/FAIL cross-check and prints the group
       table.  NEG leaves are kernel/compiled-run AGREEMENT checks, not
       certificates (same honesty note as the 20-leaf pilot).
   stageb-let <case.json> <speed.lean> <out.lean>
          [--leaves=3] [--min-size=12] [--max-lets=6] [--min-occ=2]
          [--only=both|base|let] [--tactic=decide]
       AST-dedup pilot (CertTM `LExpr` certificate-table route): fold the
       duplicated certificate-free subtrees of the case expression into a
       `Fin k → IExpr n` table + `LExpr` body with `.ref` slots, and emit
       (a) a baseline control leaf group on the ORIGINAL expression via
       `checkPosTMHull`, and (b) the let-table leaf group via
       `checkPosTMHullL` (CertTM evalTMHullD2L).  Boxes/TMParams are
       harvested from the existing `C549HullSpeed.lean`-style module
       (<speed.lean>, `def <mod>Box<j>` / `def <mod>P<j>` / leaf verdicts).
       Selection contract: only subtrees with no sqrt/div/trans/ite/abs
       nodes are folded, so the kernel `ps` certificate queue order is
       bit-identical to the unfolded tree and the harvested TMParams stay
       valid verbatim (no stage-A re-run needed).  `--only` gates which
       theorem groups are emitted so baseline vs let decide times can be
       measured in separate builds.
"""
import json
import mmap
import re
import sys
import time

from emit_lean import (box_frac, box_lit, die, hull_expr, hull_stage_a_file,
                       parse_hull_params)

LEAF_PAT = re.compile(rb'(?<=\n    )\{"box"')
HIT_TM = b'"hit": "tm"'


# ---------------------------------------------------------------------------
# stageb-let: AST dedup (LExpr certificate table) — text s-expression layer.
# The emitted IExpr text is fully parenthesized with single spaces
# (`(.op arg1 arg2)`), so a paren tokenizer + substring slices reproduce the
# exact original text without any re-formatting drift.
# ---------------------------------------------------------------------------

CERT_OPS = {".sqrt", ".div", ".trans", ".ite", ".abs"}


class N:
    """Expression node: op token, children, exact span, id, guard flag."""

    __slots__ = ("kids", "start", "end", "nid", "guard")

    def __init__(self, kids, start, end, nid):
        self.kids = kids          # list of str tokens and N nodes
        self.start, self.end = start, end
        self.nid = nid
        self.guard = False

    @property
    def op(self):
        return self.kids[0]

    def text(self, src):
        return src[self.start:self.end]


def parse_sexpr(src):
    """Parse the emitted expr text into an N tree (exact spans)."""
    toks = [(m.group(0), m.start()) for m in
            re.finditer(r'\(|\)|[^\s()]+', src)]

    def rec(pos, nid):
        assert toks[pos][0] == '(', f"expected ( at {pos}"
        st = toks[pos][1]
        pos += 1
        node = N([], st, None, nid[0])
        nid[0] += 1
        while toks[pos][0] != ')':
            if toks[pos][0] == '(':
                child, pos = rec(pos, nid)
                node.kids.append(child)
            else:
                node.kids.append(toks[pos][0])
                pos += 1
        node.end = toks[pos][1] + 1
        return node, pos + 1

    tree, pos = rec(0, [0])
    assert pos == len(toks), "trailing tokens"
    return tree


def node_size(n):
    return 1 + sum(node_size(k) for k in n.kids if isinstance(k, N))


def node_cost(n):
    """Decide-cost proxy: tree size plus, per closed-trans node, its rung N
    (the alternating series evaluates ~N big-dyadic terms — the duplicated
    rung-2048 `arctan(1)` constant dominates its 3-node AST footprint)."""
    c = 1
    if n.op == ".trans" and not has_var(n.kids[2]):
        c += int(n.kids[3])
    return c + sum(node_cost(k) for k in n.kids if isinstance(k, N))


def cert_free(n):
    """True iff evaluating `n` via `evalTMHullD2` consumes no TMParams
    certificates: no sqrt/div nodes, no ite/abs, and every trans node has a
    var-free (closed) child — the closed-trans arm evaluates the interval
    directly and consumes nothing (this is what lets the 4x-duplicated
    `arctan(1)` rung-2048 constant into the table)."""
    if n.op in (".sqrt", ".div", ".ite", ".abs"):
        return False
    if n.op == ".trans":
        return not has_var(n.kids[2])
    return all(cert_free(k) for k in n.kids if isinstance(k, N))


def has_var(n):
    if n.op == ".var":
        return True
    return any(has_var(k) for k in n.kids if isinstance(k, N))


def mark_guards(root):
    """Flag every node living under some ite cond (refs never go there:
    the LExpr guard position stays a plain ref-free IExpr)."""
    def rec(x, g):
        x.guard = g
        for i, k in enumerate(x.kids):
            if isinstance(k, N):
                rec(k, g or (x.op == ".ite" and i == 1))
    rec(root, False)


def contains_ref(x, taken_ids):
    if x.nid in taken_ids:
        return True
    if x.op == ".ite":
        return any(contains_ref(k, taken_ids) for k in x.kids[2:4]
                   if isinstance(k, N))
    return any(contains_ref(k, taken_ids) for k in x.kids
               if isinstance(k, N))


def cmd_stageb_let(case_path, speed_path, out_path, nleaves, min_size,
                   max_lets, min_occ, only, tactic):
    """AST-dedup pilot emission (see module docstring)."""
    t0 = time.time()
    if only not in ("both", "base", "let"):
        die(f"unknown --only {only!r} (both|base|let)")
    case = json.load(open(case_path))
    n = len(case["vars"])
    if n != 6:
        die(f"stageb-let MVP assumes 6 vars, case has {n}")
    expr, nsqrt, ndiv, ntrans = hull_expr(case, 128, -80)

    root = parse_sexpr(expr)
    mark_guards(root)
    total_nodes = node_size(root)

    # collect subtree occurrences at replaceable (non-guard) positions;
    # candidates must be cert-free (see cert_free) — poly ops plus closed
    # trans constants (the 4x-duplicated rung-2048 `arctan(1)`)
    occ = {}                                    # text -> [N]
    stack = [root]
    while stack:
        x = stack.pop()
        if not x.guard and x.op in (".neg", ".add", ".sub", ".mul", ".trans"):
            occ.setdefault(x.text(expr), []).append(x)
        for kk in x.kids:
            if isinstance(kk, N):
                stack.append(kk)

    # candidates: cert-free, occ >= min_occ, size >= min_size; keep a
    # maximal non-overlapping occurrence set per candidate (size desc)
    cands = []
    for txt, xs in occ.items():
        if len(xs) < min_occ or node_cost(xs[0]) < min_size:
            continue
        if not cert_free(xs[0]):
            continue
        kept = []
        for x in sorted(xs, key=lambda x: -(x.end - x.start)):
            if all(x.end <= y.start or y.end <= x.start for y in kept):
                kept.append(x)
        if len(kept) >= min_occ:
            cands.append((node_cost(xs[0]) * len(kept), len(kept),
                          node_cost(xs[0]), txt, kept))
    cands.sort(reverse=True)

    # greedy cross-candidate selection by profit, disjoint spans
    taken = []            # (txt, kept occs)
    consumed = []         # (start, end)
    for profit, nocc, size, txt, kept in cands:
        if len(taken) >= max_lets:
            break
        free = [x for x in kept
                if all(x.end <= st or en <= x.start for st, en in consumed)]
        if len(free) < min_occ:
            continue
        taken.append((txt, free))
        consumed.extend((x.start, x.end) for x in free)
    if not taken:
        die("no duplicated cert-free subtrees found — nothing to fold")
    taken_ids = {x.nid for _, free in taken for x in free}
    idx = {txt: i for i, (txt, _) in enumerate(taken)}

    def emit_body(x):
        """LExpr text for a node at a TM (non-guard) position."""
        def tok(kk):
            return kk.text(expr) if isinstance(kk, N) else kk
        if x.nid in taken_ids:
            return f"(.ref ⟨{idx[x.text(expr)]}, by decide⟩)"
        if not contains_ref(x, taken_ids):
            return f"(.plain {x.text(expr)})"
        op = x.op
        if op in (".add", ".sub", ".mul"):
            return f"({op} {emit_body(x.kids[1])} {emit_body(x.kids[2])})"
        if op == ".neg":
            return f"(.neg {emit_body(x.kids[1])})"
        if op == ".div":
            return (f"(.div {emit_body(x.kids[1])} {emit_body(x.kids[2])} "
                    f"{tok(x.kids[3])})")
        if op == ".sqrt":
            return (f"(.sqrt {emit_body(x.kids[1])} {tok(x.kids[2])} "
                    f"{tok(x.kids[3])})")
        if op == ".trans":
            return (f"(.trans {tok(x.kids[1])} {emit_body(x.kids[2])} "
                    f"{tok(x.kids[3])} {tok(x.kids[4])})")
        if op == ".ite":
            return (f"(.ite {x.kids[1].text(expr)} "
                    f"{emit_body(x.kids[2])} {emit_body(x.kids[3])})")
        die(f"emit_body: unsupported op {op} on a ref-bearing path")

    body = emit_body(root)
    table_txt = ", ".join(t for t, _ in taken)
    k = len(taken)
    n_ref = body.count("(.ref ")
    slot_desc = ", ".join(f"#{i}: {len(f)} refs x {t.count('(.') + 1} nodes"
                          for i, (t, f) in enumerate(taken))

    # harvest boxes/params/verdicts from the existing speed module
    speed = open(speed_path).read()
    boxes = {}
    for m in re.finditer(
            r"def \w+Box(\d+) : Fin 6 → DInterval :=\n  (.+)", speed):
        boxes[int(m.group(1))] = m.group(2)
    params = {}
    for m in re.finditer(r"def \w+P(\d+) : TMParams := (.+)", speed):
        params[int(m.group(1))] = m.group(2)
    verdicts = {}
    for m in re.finditer(
            r"theorem \w+Leaf(\d+) :\n\s+checkPosTMHull \w+ "
            r"\w+Box\1 \w+P\1 = (true|false) := by\n\s+(\w+)", speed):
        verdicts[int(m.group(1))] = (m.group(2), m.group(3))
    if not boxes or not params or not verdicts:
        die(f"could not harvest Box/P/verdict defs from {speed_path}")

    mod = "C549HullLet"
    parts = []
    for j in sorted(verdicts):
        if j > nleaves:
            break
        tgt, tac = verdicts[j]
        parts.append(
            f"/-- Leaf {j} box + TMParams (harvested from the speed lab;\n"
            f"stage-A verdict {tgt}). -/\n"
            f"def {mod}Box{j} : Fin {n} → DInterval :=\n  {boxes[j]}\n\n"
            f"def {mod}P{j} : TMParams := {params[j]}\n")
        if only in ("both", "base") and tac == "decide":
            parts.append(
                f"/-- Baseline control leaf {j} (unfolded expression,\n"
                f"kernel `checkPosTMHull`; plain-kernel `decide` vehicle). -/\n"
                f"theorem {mod}BaseLeaf{j} :\n"
                f"    checkPosTMHull {mod}BaseExpr {mod}Box{j} {mod}P{j} = "
                f"{tgt} := by\n  {tac}\n")
        if only in ("both", "let"):
            parts.append(
                f"/-- Let-table leaf {j} (folded expression, kernel\n"
                f"`checkPosTMHullL`; same box/params — certificate-free\n"
                f"fold, ps queue order preserved). -/\n"
                f"theorem {mod}Leaf{j} :\n"
                f"    checkPosTMHullL {mod}Tbl {mod}Body {mod}Box{j} {mod}P{j}"
                f" = {tgt} := by\n  {tactic}\n")

    hdr_extra = (
        f" — AST DEDUP MVP (CertTM LExpr certificate table):\n"
        f"  table slots {k} ({slot_desc}), body refs {n_ref},\n"
        f"  unfolded {total_nodes} nodes; certificate-free fold so the\n"
        f"  harvested TMParams are consumed in the original order;\n"
        f"  baseline/let groups gated by --only for isolated timing.")
    axioms_line = (f"\n#print axioms {mod}Leaf1\n"
                   if only in ("both", "let") else "")
    text = (
        f"/-\n"
        f"  549 decide-speed lab, AST-dedup pilot (auto-generated by\n"
        f"  pipeline/interval/emit_hull_pilot.py stageb-let).\n"
        f"  case: {case['id']}  (orig_op: {case.get('orig_op')},\n"
        f"  vars: {case['vars']}){hdr_extra}\n"
        f"-/\n"
        f"import Kepler.Interval.CertTM\n\n"
        f"set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
        f"namespace Kepler.Interval.Cases\n\n"
        f"/-- The unfolded case expression (baseline control, verbatim\n"
        f"hull-route emission). -/\n"
        f"def {mod}BaseExpr : IExpr {n} :=\n  {expr}\n\n"
        f"/-- The certificate table (duplicated certificate-free subtrees,\n"
        f"first-occurrence order; entries consume no certificates). -/\n"
        f"def {mod}Tbl : Fin {k} → IExpr {n} := ![{table_txt}]\n\n"
        f"/-- The folded body (shared slots referenced via `.ref`; the\n"
        f"ite guard position stays a plain ref-free `IExpr`). -/\n"
        f"def {mod}Body : LExpr {n} {k} :=\n  {body}\n\n"
        + "\n".join(parts) +
        axioms_line +
        f"\nend Kepler.Interval.Cases\n")
    open(out_path, "w").write(text)
    print(f"[stageb-let] wrote {out_path}  ({time.time() - t0:.1f}s)")
    print(f"[stageb-let] unfolded nodes {total_nodes}  table slots {k}  "
          f"body refs {n_ref}")
    for i, (t, f) in enumerate(taken):
        print(f"[stageb-let]   slot {i}: {len(f)} refs x "
              f"{t.count('(.') + 1} nodes  head {t[:60]}")


def load_boxes(path):
    """boxes.json -> list of dyadic-pair dim tuples (emit_lean form)."""
    data = json.load(open(path))
    if len(data["boxes"]) != data.get("n", len(data["boxes"])):
        die(f"boxes.json n={data.get('n')} != {len(data['boxes'])} entries")
    return data["case"], [tuple(box_frac(iv) for iv in dim)
                          for dim in data["boxes"]]


def cmd_stagea(case_path, boxes_path, out_path, gran, rung_n, rung_out):
    """Stage-A probe driver emission (emit_lean --hull stage-A semantics)."""
    t0 = time.time()
    case = json.load(open(case_path))
    cid, boxes = load_boxes(boxes_path)
    if cid != case["id"]:
        die(f"boxes case {cid} != case id {case['id']}")
    n = len(case["vars"])
    expr, nsqrt, ndiv, ntrans = hull_expr(case, rung_n, rung_out)
    meta = dict(caseid=case["id"], origop=case.get("orig_op"),
                vars=case["vars"], prec="-")
    out = hull_stage_a_file(
        "C549HullA200", n, expr, boxes, gran, rung_n, rung_out,
        nsqrt, ndiv, ntrans, len(boxes), meta,
        f" — SCHEMA-V3 HULLD LAUNCH DRILL stage A: {len(boxes)} tm leaves "
        f"(stride sample of {case['id']})")
    open(out_path, "w").write(out)
    print(f"[stagea] wrote {out_path}  ({time.time() - t0:.1f}s)  "
          f"sqrt {nsqrt}  div {ndiv}  trans {ntrans};  run from lean/: "
          f"lake env lean --run {out_path} > params.txt")


def parse_hullstats(path):
    """--probe --hull-stats output -> {i: (valid, closed, mode)}."""
    modes = {}
    for ln in open(path):
        if not ln.startswith('{"i"'):
            continue
        d = json.loads(ln)
        modes[d["i"]] = (d.get("valid", 0), d.get("closed", 0),
                         d.get("mode", "?"))
    return modes


def cmd_stageb(case_path, boxes_path, params_path, stats_path, out_path,
               shard_size, tactic):
    """Stage-B kernel pilot emission with shard sections + summary."""
    t0 = time.time()
    if tactic not in ("decide", "native_decide"):
        die(f"unknown tactic {tactic!r} (decide|native_decide)")
    case = json.load(open(case_path))
    cid, boxes = load_boxes(boxes_path)
    if cid != case["id"]:
        die(f"boxes case {cid} != case id {case['id']}")
    n = len(case["vars"])
    expr, nsqrt, ndiv, ntrans = hull_expr(case, 128, -80)
    rung, verdicts = parse_hull_params(params_path, nsqrt)
    modes = parse_hullstats(stats_path)
    if sorted(verdicts) != list(range(len(boxes))):
        die(f"params cover {sorted(verdicts)[:3]}..., expected 0..{len(boxes) - 1}")
    if sorted(modes) != list(range(len(boxes))):
        die(f"hullstats covers {len(modes)} boxes, expected {len(boxes)}")

    rows = []
    for k in sorted(verdicts):
        verdict, lo_m, lo_e, trip = verdicts[k]
        valid, closed, mode = modes[k]
        if not valid or not closed:
            die(f"leaf {k}: C-side valid={valid} closed={closed} — not a "
                f"cert leaf, sample/manifest mismatch?")
        rows.append((k, boxes[k], verdict, lo_m, lo_e, trip, mode))

    n_pass = sum(1 for r in rows if r[2] == "PASS")
    n_single = sum(1 for r in rows if r[6] == "single")
    n_strad = len(rows) - n_single
    s_pass = sum(1 for r in rows if r[6] == "single" and r[2] == "PASS")
    t_pass = sum(1 for r in rows if r[6] != "single" and r[2] == "PASS")

    mod = "C549Hull200"
    npar, out_e, g0, g1, g2, g3, g4, g5, g6 = rung
    parts = []
    all_props = []
    nshards = (len(rows) + shard_size - 1) // shard_size
    for s in range(nshards):
        chunk = rows[s * shard_size:(s + 1) * shard_size]
        names = []
        for (k, box, verdict, lo_m, lo_e, trip, mode) in chunk:
            j = k + 1
            sq = ", ".join(f"⟨{a}, {b}, {c}, ({g3}), ({g4})⟩"
                           for a, b, c in trip)
            iv = ", ".join(f"⟨({g0}), ({g1}), ({g2})⟩" for _ in range(ndiv))
            tv = ", ".join(f"⟨({g5}), ({g6})⟩" for _ in range(ntrans))
            tgt = "true" if verdict == "PASS" else "false"
            parts.append(
                f"/-- Cert leaf {k} ({mode}; stage-A margin loBound\n"
                f"{lo_m} * 2^({lo_e}); verdict {verdict}). -/\n"
                f"def {mod}Box{j} : Fin {n} → DInterval :=\n  {box_lit(box)}\n\n"
                f"def {mod}P{j} : TMParams := ⟨[{sq}], [{iv}], [{tv}]⟩\n\n"
                f"theorem {mod}Leaf{j} :\n"
                f"    checkPosTMHull {mod}Expr {mod}Box{j} {mod}P{j} = {tgt} := by\n"
                f"  {tactic}\n")
            names.append((f"{mod}Leaf{j}",
                          f"checkPosTMHull {mod}Expr {mod}Box{j} {mod}P{j} = {tgt}"))
        all_props.append(names)
        c_single = sum(1 for r in chunk if r[6] == "single")
        c_pass = sum(1 for r in chunk if r[2] == "PASS")
        goal = " ∧\n    ".join(p for _, p in names)
        conj = "⟨" + ", ".join(t for t, _ in names) + "⟩"
        parts.append(
            f"/-- Shard {s + 1}: cert leaves {chunk[0][0]}..{chunk[-1][0]} "
            f"(single {c_single}, straddle {len(chunk) - c_single},\n"
            f"PASS {c_pass}, NEG {len(chunk) - c_pass}); kernel/compiled-run\n"
            "agreement on every leaf; references the leaf theorems — no\n"
            "recomputation. -/\n"
            f"theorem {mod}Shard{s + 1} :\n    {goal} :=\n  {conj}\n")

    extra = (f" — SCHEMA-V3 HULLD LAUNCH DRILL stage B: kernel verdicts on "
             f"{len(rows)} of 281894 tm leaves\n  (single {n_single} "
             f"[PASS {s_pass}], straddle {n_strad} [PASS {t_pass}]); "
             f"{n_pass} PASS, {len(rows) - n_pass} NEG; NEG\n  leaves are "
             "NOT certificates — the lemma proven per leaf is the\n"
             "  kernel/compiled-run agreement (see CertTM.lean M2b section)"
             + ("" if tactic == "decide" else
                f"\n  PROOF VEHICLE: {tactic} — trust base adds the Lean"
                " compiler+runtime; one scoped\n  `Lean.ofReduceBool`-shaped"
                " axiom per leaf theorem (DECISIONS.md 2026-08-10 shape);"
                "\n  scope extension beyond Graphs.Cert*/Assembly.GoodList*"
                " needs its own DECISIONS.md entry"))
    hdr = ("""/-
  Phase 4, G4 certificate (auto-generated by pipeline/interval/emit_hull_pilot.py).
  case: {caseid}  (orig_op: {origop}, vars: {vars})
  cert: {nleaves} leaf/leaves, prec {prec} (bb_arb){extra}
  Do not edit by hand.
-/""")
    flat = [pair for names in all_props for pair in names]
    goal = " ∧\n    ".join(p for _, p in flat)
    conj = "⟨" + ", ".join(t for t, _ in flat) + "⟩"
    text = (hdr.format(caseid=case["id"], origop=case.get("orig_op"),
                       vars=case["vars"], nleaves=len(rows), prec="-",
                       extra=extra) +
            "\nimport Kepler.Interval.CertTM\n\n"
            "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            "/-- The case expression for the hull route (dummy sqrt slots;\n"
            f"atan rungs baked: open ({npar}, ({out_e})), closed (2048, -64)). -/\n"
            f"def {mod}Expr : IExpr {n} :=\n  {expr}\n\n"
            + "\n".join(parts) +
            "\n/-- Launch-drill summary: the full leaf-property conjunction\n"
            "(the shards state the same props per 50-leaf group; operands of\n"
            "`∧` must be propositions, so the summary mirrors the leaf props\n"
            "and closes with the leaf theorems — no recomputation). -/\n"
            f"theorem {mod}_pilot :\n    {goal} :=\n  {conj}\n\n"
            f"#print axioms {mod}_pilot\n\n"
            "end Kepler.Interval.Cases\n")
    open(out_path, "w").write(text)
    dt = time.time() - t0
    print(f"[stageb] wrote {out_path}  ({dt:.1f}s)  {len(rows)} leaves, "
          f"{nshards} shards x <= {shard_size} decides")
    print("[group] expected: single -> PASS, straddle -> NEG (Lean hull pays "
          "full hull width as err)")
    print(f"[group] single   : {n_single:4d}  PASS {s_pass:4d}  NEG "
          f"{n_single - s_pass:4d}")
    print(f"[group] straddle : {n_strad:4d}  PASS {t_pass:4d}  NEG "
          f"{n_strad - t_pass:4d}")
    mism = [(r[0], r[6], r[2]) for r in rows
            if (r[2] == "PASS") != (r[6] == "single")]
    if mism:
        print(f"[group] NOTE {len(mism)} straddle leaves PASS anyway (positive "
              f"margin survives the hull-width err premium): "
              f"{[m[0] for m in mism]}")
    else:
        print("[group] cross-check vs C-side --hull-stats: 100% aligned")


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    opts = {}
    for a in sys.argv[1:]:
        if a.startswith("--") and "=" in a:
            k, v = a[2:].split("=", 1)
            opts[k] = v
    if not args:
        die(__doc__)
    cmd = args[0]
    if cmd == "sample":
        cmd_sample(args[1], args[2], args[3], int(opts.get("k", 200)))
    elif cmd == "stagea":
        cmd_stagea(args[1], args[2], args[3], int(opts.get("gran", -80)),
                   int(opts.get("rung", 128)), int(opts.get("rung-out", -80)))
    elif cmd == "stageb":
        cmd_stageb(args[1], args[2], args[3], args[4], args[5],
                   int(opts.get("shard", 50)),
                   opts.get("tactic", "decide"))
    elif cmd == "stageb-let":
        cmd_stageb_let(args[1], args[2], args[3],
                       int(opts.get("leaves", 3)),
                       int(opts.get("min-size", 12)),
                       int(opts.get("max-lets", 6)),
                       int(opts.get("min-occ", 2)),
                       opts.get("only", "both"),
                       opts.get("tactic", "decide"))
    else:
        die(f"unknown subcommand {cmd}")


if __name__ == "__main__":
    main()
