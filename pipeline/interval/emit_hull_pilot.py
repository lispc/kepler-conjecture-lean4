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
  pick-straddle <boxes.json> <hullstats.jsonl> <case.json> <out-prefix>
                [--cap=160]
      Filter a sampled boxes file (after a bb_arb --probe --hull-stats
      classification pass) to valid+closed `straddle_hull` leaves,
      renumbered 0..M-1: writes <prefix>.boxes.json /
      <prefix>.hullstats.jsonl / <prefix>.manifest.json (kept cert leaf
      indices, drop accounting, exact-rational ite-guard census per leaf —
      the advisory root-guard straddle criterion).
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
    stageb-shards <case.json> <boxes.json> <params.txt> <hullstats.jsonl>
                  <out-dir> [--mod=C549StraddleBatch] [--shard=20]
                  [--rung=128] [--tactic=decide] [--compare=<params2.txt>]
        Straddle BATCH kernel pilot (production HullD2 half): one Base
        module (the case expr), one module per <=shard-leaf group
        (`checkPosTMHull ... = true|false` per leaf + shard conjunction,
        separate modules so `lake build` can compile them in parallel), a
        summary module over the shard theorems, and a manifest joining
        verdicts / loBounds / hullstats (plus an optional second stage-A
        params file — e.g. the rung-2048 arm — for the rung comparison).
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
    stagea-let <case.json> <speed.lean> <out_driver.lean>
           [--leaves=3] [--min-size=12] [--max-lets=6] [--min-occ=2]
           [--gran=-80] [--rung=128] [--rung-out=-80]
        Stage-A-let probe driver for the FULL fold (certificate-consuming
        subtrees folded too — same planner as stageb-let with the
        certificate-free gate lifted).  Emits a compiled-run driver
        evaluating `tmHullLeafProbeL` per leaf (CertTM evalTMHullFill2L:
        table entries first in index order, then the body, guard-first)
        printing the RUNG header then per-leaf
        `<i> PASS|NEG <lo_m> <lo_e> <slo shi sc>...` lines — the mantissa
        queue in the NEW consumption order.  Run with
        `lake env lean --run` from the `lean/` package root; output is a
        stageb-let2 params file.  A manifest (fold stats, harvest
        provenance, probe command) is written next to the driver.
    stageb-let2 <case.json> <speed.lean> <params.txt> <out.lean>
           [--leaves=3] [--min-size=12] [--max-lets=6] [--min-occ=2]
           [--tactic=decide] [--split-dir=DIR]
        Kernel pilot for the FULL fold: re-plans the identical fold
        (deterministic given the flags), joins the stagea-let probe
        params per leaf, and emits the combined module (per-leaf
        `checkPosTMHullL <mod>Tbl <mod>Body <mod>Box<j> <mod>P<j> = true`
        decide theorems + `#print axioms`) plus a manifest.  With
        `--split-dir=DIR` it additionally writes per-leaf single-theorem
        timing modules for all three arms — base (unfolded
        `checkPosTMHull`), free (certificate-free fold, MVP params),
        full (full fold, probe params) — for isolated `lake build` /
        `lake env lean` timing.  Architectural note: folding
        certificate-consuming subtrees permutes the `ps` queue (entries
        evaluate first), so the C-side certificates no longer line up
        positionally — the params of the full-fold route can only be
        produced by the Lean compiled probe (two-layer pipeline: C emits
        boxes, Lean re-produces params).
 """
import json
import mmap
import os
import re
import sys
import time

from emit_lean import (box_frac, box_lit, die, hull_expr, hull_stage_a_file,
                       parse_hull_params)

LEAF_PAT = re.compile(rb'(?<=\n    )\{"box"')
HIT_TM = b'"hit": "tm"'


def cmd_sample(cert_path, boxes_path, manifest_path, k):
    """Stride sample k tm-hit leaves through mmap offsets (probe_l1 style)."""
    t0 = time.time()
    with open(cert_path, "rb") as f:
        mm = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
        starts = [m.start() for m in LEAF_PAT.finditer(mm)]
        n_total = len(starts)
        # per-leaf hit test: the `"hit":` field follows the box array inside
        # each leaf object — search a bounded window (box lines are <1KB)
        n_tm = 0
        for off in starts:
            if mm.find(HIT_TM, off, off + 8192) != -1:
                n_tm += 1
        if n_tm < k:
            die(f"cert has {n_tm} tm leaves < requested {k}")
        stride = max(1, n_tm // k)
        dec = json.JSONDecoder()
        picks = []
        picked_idx = []
        ti = 0
        for li, off in enumerate(starts):
            is_tm = mm.find(HIT_TM, off, off + 8192) != -1
            if is_tm:
                if ti % stride == 0:
                    obj, _ = dec.raw_decode(
                        mm[off:off + 16384].decode("utf-8", "replace"), 0)
                    if "box" not in obj:
                        die(f"leaf decode at offset {off} has no box")
                    picks.append(obj["box"])
                    picked_idx.append(li)
                ti += 1
                if len(picks) >= k:
                    break
        head = mm[:200].decode("utf-8", "replace")
        mm.close()
    m = re.search(r'"id"\s*:\s*"([^"]+)"', head)
    if not m:
        die(f"could not read case id from cert head: {head[:60]}...")
    caseid = m.group(1)
    json.dump({"case": caseid, "n": len(picks), "boxes": picks},
              open(boxes_path, "w"))
    json.dump({"schema": "hull-pilot-sample", "case": caseid,
               "cert": cert_path, "k": k, "stride": stride,
               "n_total": n_total, "n_tm": n_tm,
               "picked_leaf_indices": picked_idx},
              open(manifest_path, "w"), indent=1)
    dt = time.time() - t0
    print(f"[sample] case {caseid}  leaves {n_total}  tm {n_tm}  "
          f"stride {stride}  picked {len(picks)}  ({dt:.1f}s)  "
          f"-> {boxes_path}")
    print(f"[sample] picked cert leaf indices 0..{picked_idx[-1]} "
          f"(first {picked_idx[:3]} ... last {picked_idx[-3:]})")


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


def plan_fold(case, min_size, max_lets, min_occ, cert_free_only):
    """Shared fold planner for the stageb-let family.

    Collects duplicated subtree texts at replaceable (non-guard)
    positions of the emitted hull-route expression, scores candidates by
    `node_cost * occurrences`, and greedily takes a profit-ordered,
    span-disjoint selection bounded by `max_lets` (identical planning in
    stagea-let and stageb-let2: the flags fully determine the fold).

    With `cert_free_only` (stageb-let MVP contract) only subtrees whose
    evaluation consumes no TMParams certificate are foldable, so the
    harvested params stay valid verbatim.  With the gate lifted (full
    fold) sqrt/div/trans-bearing duplicates enter the table too — the ps
    consumption ORDER then changes (entries evaluate first, index order,
    before any body node), so params must be re-produced per leaf by the
    stagea-let compiled probe (`tmHullLeafProbeL`); the C-side
    certificate correspondence is broken positionally (architecture
    note in the module docstring).

    Returns a dict: expr / nsqrt / ndiv / ntrans / total_nodes / taken
    [(text, kept occurrences)] / body / table_txt / k / n_ref /
    slot_desc."""
    expr, nsqrt, ndiv, ntrans = hull_expr(case, 128, -80)
    root = parse_sexpr(expr)
    mark_guards(root)
    total_nodes = node_size(root)

    # collect subtree occurrences at replaceable (non-guard) positions;
    # with cert_free_only the candidates must be cert-free (see
    # cert_free) — poly ops plus closed trans constants; otherwise
    # certificate-consuming duplicates (div/sqrt/trans chains) fold too
    occ = {}                                    # text -> [N]
    stack = [root]
    while stack:
        x = stack.pop()
        if not x.guard and x.op in (".neg", ".add", ".sub", ".mul",
                                    ".trans", ".div", ".sqrt"):
            occ.setdefault(x.text(expr), []).append(x)
        for kk in x.kids:
            if isinstance(kk, N):
                stack.append(kk)

    # candidates: (cert-free), occ >= min_occ, size >= min_size; keep a
    # maximal non-overlapping occurrence set per candidate (size desc)
    cands = []
    for txt, xs in occ.items():
        if len(xs) < min_occ or node_cost(xs[0]) < min_size:
            continue
        if cert_free_only and not cert_free(xs[0]):
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
    body = emit_fold_body(root, expr, {x.nid for _, free in taken
                                       for x in free},
                          {txt: i for i, (txt, _) in enumerate(taken)})
    table_txt = ", ".join(t for t, _ in taken)
    k = len(taken)
    n_ref = body.count("(.ref ")
    slot_desc = ", ".join(f"#{i}: {len(f)} refs x {t.count('(.') + 1} nodes"
                          for i, (t, f) in enumerate(taken))
    return dict(expr=expr, nsqrt=nsqrt, ndiv=ndiv, ntrans=ntrans,
                total_nodes=total_nodes, taken=taken, body=body,
                table_txt=table_txt, k=k, n_ref=n_ref, slot_desc=slot_desc)


def emit_fold_body(root, expr, taken_ids, idx):
    """LExpr body text for the planned fold (see plan_fold)."""
    def tok(kk):
        return kk.text(expr) if isinstance(kk, N) else kk

    def rec(x):
        if x.nid in taken_ids:
            return f"(.ref ⟨{idx[x.text(expr)]}, by decide⟩)"
        if not contains_ref(x, taken_ids):
            return f"(.plain {x.text(expr)})"
        op = x.op
        if op in (".add", ".sub", ".mul"):
            return f"({op} {rec(x.kids[1])} {rec(x.kids[2])})"
        if op == ".neg":
            return f"(.neg {rec(x.kids[1])})"
        if op == ".div":
            return (f"(.div {rec(x.kids[1])} {rec(x.kids[2])} "
                    f"{tok(x.kids[3])})")
        if op == ".sqrt":
            return (f"(.sqrt {rec(x.kids[1])} {tok(x.kids[2])} "
                    f"{tok(x.kids[3])})")
        if op == ".trans":
            return (f"(.trans {tok(x.kids[1])} {rec(x.kids[2])} "
                    f"{tok(x.kids[3])} {tok(x.kids[4])})")
        if op == ".ite":
            return (f"(.ite {x.kids[1].text(expr)} "
                    f"{rec(x.kids[2])} {rec(x.kids[3])})")
        die(f"emit_fold_body: unsupported op {op} on a ref-bearing path")
    return rec(root)


def harvest_speed(speed_path):
    """Boxes / TMParams / verdicts harvested from a C549Hull*-style speed
    module (the stageb-let-family provenance contract)."""
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
    return boxes, params, verdicts


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
    plan = plan_fold(case, min_size, max_lets, min_occ, cert_free_only=True)
    expr, total_nodes = plan["expr"], plan["total_nodes"]

    # harvest boxes/params/verdicts from the existing speed module
    boxes, params, verdicts = harvest_speed(speed_path)

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
        f"  table slots {plan['k']} ({plan['slot_desc']}), body refs "
        f"{plan['n_ref']},\n  unfolded {total_nodes} nodes; certificate-free "
        f"fold so the\n  harvested TMParams are consumed in the original "
        f"order;\n  baseline/let groups gated by --only for isolated timing.")
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
        f"def {mod}Tbl : Fin {plan['k']} → IExpr {n} := "
        f"![{plan['table_txt']}]\n\n"
        f"/-- The folded body (shared slots referenced via `.ref`; the\n"
        f"ite guard position stays a plain ref-free `IExpr`). -/\n"
        f"def {mod}Body : LExpr {n} {plan['k']} :=\n  {plan['body']}\n\n"
        + "\n".join(parts) +
        axioms_line +
        f"\nend Kepler.Interval.Cases\n")
    open(out_path, "w").write(text)
    print(f"[stageb-let] wrote {out_path}  ({time.time() - t0:.1f}s)")
    print(f"[stageb-let] unfolded nodes {total_nodes}  table slots "
          f"{plan['k']}  body refs {plan['n_ref']}")
    for i, (t, f) in enumerate(plan["taken"]):
        print(f"[stageb-let]   slot {i}: {len(f)} refs x "
              f"{t.count('(.') + 1} nodes  head {t[:60]}")


def params_lit(rung, ndiv, ntrans, trips):
    """TMParams literal from the RUNG header granularities plus one leaf's
    stage-A(-let) mantissa-triple queue (sqrt certs carry the mantissas;
    inv/trans certs are granularity records, order-insensitive)."""
    npar, out_e, g0, g1, g2, g3, g4, g5, g6 = rung
    sq = ", ".join(f"⟨{a}, {b}, {c}, ({g3}), ({g4})⟩" for a, b, c in trips)
    iv = ", ".join(f"⟨({g0}), ({g1}), ({g2})⟩" for _ in range(ndiv))
    tv = ", ".join(f"⟨({g5}), ({g6})⟩" for _ in range(ntrans))
    return f"⟨[{sq}], [{iv}], [{tv}]⟩"


def cmd_stagea_let(case_path, speed_path, out_path, nleaves, min_size,
                   max_lets, min_occ, gran, rung_n, rung_out):
    """Stage-A-let probe driver emission for the FULL fold (see module
    docstring): compiled-run `tmHullLeafProbeL` per leaf, producing the
    mantissa queue in the new (entries-first) ps consumption order."""
    t0 = time.time()
    case = json.load(open(case_path))
    n = len(case["vars"])
    if n != 6:
        die(f"stagea-let MVP assumes 6 vars, case has {n}")
    plan = plan_fold(case, min_size, max_lets, min_occ, cert_free_only=False)
    boxes, params, verdicts = harvest_speed(speed_path)
    leaves = [j for j in sorted(verdicts) if j <= nleaves]
    if len(leaves) != nleaves:
        die(f"speed module covers verdict leaves {sorted(verdicts)[:3]}..., "
            f"need 1..{nleaves}")
    nsqrt, ndiv, ntrans = plan["nsqrt"], plan["ndiv"], plan["ntrans"]
    if nsqrt == 0:
        die("no sqrt nodes — mantissa params would be empty (unexpected "
            "for the 549 hull route)")
    g = f"({gran})"
    mod = "C549HullLet2A"
    boxes_lean = ",\n    ".join(
        f"({boxes[j]} : Fin {n} → DInterval)" for j in leaves)
    manifest = {
        "schema": "stagea-let",
        "case": case["id"],
        "driver": out_path,
        "params_out": out_path.rsplit(".lean", 1)[0] + ".params.txt",
        "probe_cmd": f"lake env lean --run {out_path} > {out_path.rsplit('.lean', 1)[0] + '.params.txt'}",
        "fold": {"min_size": min_size, "max_lets": max_lets,
                 "min_occ": min_occ, "cert_free_only": False,
                 "slots": plan["k"], "body_refs": plan["n_ref"],
                 "unfolded_nodes": plan["total_nodes"],
                 "slot_desc": plan["slot_desc"]},
        "counts": {"sqrt": nsqrt, "div": ndiv, "trans": ntrans},
        "template": {"rung_n": rung_n, "rung_out": rung_out, "gran": gran},
        "ps_contract": "entries first in index order, then body, "
                       "guard-first; mantissa triples report that order",
        "leaves": [{"j": j, "speed_verdict": verdicts[j][0],
                    "params_source": f"{speed_path}:P{j}"} for j in leaves],
        "harvest": speed_path,
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "emit_elapsed_s": round(time.time() - t0, 1),
    }
    # only HDR-ish f-strings; the probe loop keeps its Lean braces literal
    text = (
        f"/-\n"
        f"  549 stage-A-let probe driver (auto-generated by\n"
        f"  pipeline/interval/emit_hull_pilot.py stagea-let).\n"
        f"  case: {case['id']}  (orig_op: {case.get('orig_op')},\n"
        f"  vars: {case['vars']}) — FULL FOLD (certificate-consuming\n"
        f"  subtrees folded): table slots {plan['k']} "
        f"({plan['slot_desc']}),\n  body refs {plan['n_ref']}, unfolded "
        f"{plan['total_nodes']} nodes.\n"
        f"  ps contract: table entries evaluate first in index order,\n"
        f"  then the body, guard-first at ite nodes — exactly the order\n"
        f"  tmHullLeafProbeL reports (mantissa triples; inv/trans certs\n"
        f"  are granularity records).  These params are the ONLY valid\n"
        f"  ones for the folded route: the C-side certificate order is\n"
        f"  broken positionally by the fold (two-layer pipeline: C emits\n"
        f"  boxes, Lean re-produces params).\n"
        f"  Run from lean/: lake env lean --run {out_path} > params.txt\n"
        f"-/\n"
        f"import Kepler.Interval.CertTM\n\n"
        f"set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
        f"open Kepler.Interval\n\n"
        f"/-- Local default (for `Array.get!` in the probe loop only). -/\n"
        f"instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩\n\n"
        f"/-- The certificate table (FULL fold: certificate-consuming\n"
        f"duplicates included; entries consume ps certs first). -/\n"
        f"def {mod}Tbl : Fin {plan['k']} → IExpr {n} := "
        f"![{plan['table_txt']}]\n\n"
        f"/-- The folded body (shared slots referenced via `.ref`; the\n"
        f"ite guard positions stay plain ref-free `IExpr`). -/\n"
        f"def {mod}Body : LExpr {n} {plan['k']} :=\n  {plan['body']}\n\n"
        f"/-- Template TMParams: dummy mantissas, pilot recip granularity\n"
        f"{gran} everywhere. -/\n"
        f"def {mod}Ps : TMParams :=\n"
        f"  ⟨List.replicate {nsqrt} ⟨0, 0, 0, {g}, {g}⟩,\n"
        f"   List.replicate {ndiv} ⟨{g}, {g}, {g}⟩,\n"
        f"   List.replicate {ntrans} ⟨{g}, {g}⟩⟩\n\n"
        f"/-- The {nleaves} harvested speed-lab leaf boxes. -/\n"
        f"def {mod}Boxes : Array (Fin {n} → DInterval) :=\n  #["
        + boxes_lean + "]\n\n"
        "def main : List String → IO UInt32 := fun _ => do\n"
        f"  IO.println \"RUNG {rung_n} {rung_out} {g} {g} {g} {g} {g} {g} {g}\"\n"
        f"  for i in [0:{mod}Boxes.size] do\n"
        f"    let t0 ← IO.monoMsNow\n"
        f"    match tmHullLeafProbeL {mod}Tbl {mod}Body {mod}Boxes[i]! {mod}Ps with\n"
        "    | some (p, m, e, l) =>\n"
        "        let ms ← IO.monoMsNow\n"
        "        let v := if p then \"PASS\" else \"NEG\"\n"
        "        let trip := String.intercalate \" \"\n"
        "          (l.map fun t => s!\"{t.1} {t.2.1} {t.2.2}\")\n"
        "        IO.eprintln s!\"probe {i}: {ms - t0} ms\"\n"
        "        IO.println s!\"{i} {v} {m} {e} {trip}\"\n"
        "    | none =>\n"
        "        let ms ← IO.monoMsNow\n"
        "        IO.eprintln s!\"probe {i}: {ms - t0} ms FAIL\"\n"
        "        IO.println s!\"{i} FAIL\"\n"
        "  return 0\n")
    open(out_path, "w").write(text)
    json.dump(manifest, open(out_path.rsplit(".lean", 1)[0] +
                             ".manifest.json", "w"), indent=1)
    print(f"[stagea-let] wrote {out_path}  ({time.time() - t0:.1f}s)  "
          f"sqrt {nsqrt}  div {ndiv}  trans {ntrans}")
    print(f"[stagea-let] FULL fold: slots {plan['k']}  body refs "
          f"{plan['n_ref']}  unfolded {plan['total_nodes']} nodes")
    for i, (t, f) in enumerate(plan["taken"]):
        cf = "cert-free" if cert_free(parse_sexpr(t)) else "cert-consuming"
        print(f"[stagea-let]   slot {i}: {len(f)} refs x "
              f"{t.count('(.') + 1} nodes  {cf}  head {t[:52]}")
    print(f"[stagea-let] run from lean/: lake env lean --run {out_path} "
          f"> {manifest['params_out']}")


def cmd_stageb_let2(case_path, speed_path, params_path, out_path, nleaves,
                    min_size, max_lets, min_occ, tactic, split_dir):
    """Kernel pilot for the FULL fold (see module docstring): identical
    fold re-planned, stage-A-let probe params joined per leaf, combined
    `checkPosTMHullL` decide module + manifest, optional per-leaf timing
    modules for the base/free/full three-way comparison."""
    t0 = time.time()
    if tactic not in ("decide", "native_decide"):
        die(f"unknown tactic {tactic!r} (decide|native_decide)")
    case = json.load(open(case_path))
    n = len(case["vars"])
    if n != 6:
        die(f"stageb-let2 MVP assumes 6 vars, case has {n}")
    plan = plan_fold(case, min_size, max_lets, min_occ, cert_free_only=False)
    plan_free = plan_fold(case, min_size, max_lets, min_occ,
                          cert_free_only=True)
    boxes, params, verdicts = harvest_speed(speed_path)
    rung, probe = parse_hull_params(params_path, plan["nsqrt"])
    leaves = [j for j in sorted(verdicts) if j <= nleaves]
    if len(leaves) != nleaves:
        die(f"speed module covers verdict leaves {sorted(verdicts)[:3]}..., "
            f"need 1..{nleaves}")
    missing = [j for j in leaves if (j - 1) not in probe]
    if missing:
        die(f"stage-A-let params cover {sorted(probe)[:3]}..., missing "
            f"leaves {missing} (re-run stagea-let with --leaves={nleaves})")
    mod = out_path.rsplit("/", 1)[-1].rsplit(".lean", 1)[0]
    rows = []
    for j in leaves:
        verd, lo_m, lo_e, trips = probe[j - 1]
        tgt, _tac = verdicts[j]
        if (verd == "PASS") != (tgt == "true"):
            print(f"[stageb-let2] WARNING leaf {j}: probe {verd} vs speed "
                  f"harvest {tgt} — emitting the probe verdict as an "
                  f"agreement check")
        rows.append((j, boxes[j], verd, lo_m, lo_e, trips))

    parts = []
    for (j, box, verd, lo_m, lo_e, trips) in rows:
        tgt = "true" if verd == "PASS" else "false"
        parts.append(
            f"/-- Leaf {j}: box from the speed lab; TMParams RE-PRODUCED\n"
            f"by the stage-A-let compiled probe (full fold: entries\n"
            f"consume certs first, so the C-side queue order no longer\n"
            f"applies); stage-A-let margin loBound {lo_m} * 2^({lo_e}),\n"
            f"verdict {verd}. -/\n"
            f"def {mod}Box{j} : Fin {n} → DInterval :=\n  {box}\n\n"
            f"def {mod}P{j} : TMParams := "
            f"{params_lit(rung, plan['ndiv'], plan['ntrans'], trips)}\n\n"
            f"/-- Full-fold leaf {j} (kernel `checkPosTMHullL`,\n"
            f"`{tactic}` vehicle): kernel/compiled-run agreement on the\n"
            f"re-produced params — PASS on the folded route. -/\n"
            f"theorem {mod}Leaf{j} :\n"
            f"    checkPosTMHullL {mod}Tbl {mod}Body {mod}Box{j} {mod}P{j}"
            f" = {tgt} := by\n  {tactic}\n")
    text = (
        f"/-\n"
        f"  549 stage-A-let kernel pilot, FULL FOLD (auto-generated by\n"
        f"  pipeline/interval/emit_hull_pilot.py stageb-let2).\n"
        f"  case: {case['id']}  (orig_op: {case.get('orig_op')},\n"
        f"  vars: {case['vars']}) — table slots {plan['k']} "
        f"({plan['slot_desc']}),\n  body refs {plan['n_ref']}, unfolded "
        f"{plan['total_nodes']} nodes.\n"
        f"  Certificate-consuming duplicates folded: the ps queue is\n"
        f"  consumed entries-first, so these TMParams are the Lean-probe\n"
        f"  re-production (stagea-let, {params_path}) — the C-side\n"
        f"  certificate correspondence is positional-broken by design\n"
        f"  (two-layer pipeline: C emits boxes, Lean re-produces params).\n"
        f"-/\n"
        f"import Kepler.Interval.CertTM\n\n"
        f"set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
        f"namespace Kepler.Interval.Cases\n\n"
        f"/-- The certificate table (FULL fold). -/\n"
        f"def {mod}Tbl : Fin {plan['k']} → IExpr {n} := "
        f"![{plan['table_txt']}]\n\n"
        f"/-- The folded body (ite guards stay plain ref-free `IExpr`). -/\n"
        f"def {mod}Body : LExpr {n} {plan['k']} :=\n  {plan['body']}\n\n"
        + "\n".join(parts) +
        f"\n#print axioms {mod}Leaf1\n"
        f"\nend Kepler.Interval.Cases\n")
    open(out_path, "w").write(text)
    n_pass = sum(1 for r in rows if r[2] == "PASS")
    manifest = {
        "schema": "stageb-let2",
        "case": case["id"],
        "module": mod, "out": out_path,
        "params_source": params_path,
        "fold": {"min_size": min_size, "max_lets": max_lets,
                 "min_occ": min_occ, "cert_free_only": False,
                 "slots": plan["k"], "body_refs": plan["n_ref"],
                 "unfolded_nodes": plan["total_nodes"],
                 "slot_desc": plan["slot_desc"]},
        "fold_free_mvp": {"slots": plan_free["k"],
                          "slot_desc": plan_free["slot_desc"]},
        "tactic": tactic,
        "leaves": [{"j": j, "probe_verdict": verd,
                    "lo_m": lo_m, "lo_e": lo_e,
                    "n_sqrt_trips": len(trips),
                    "speed_verdict": verdicts[j][0]}
                   for (j, _, verd, lo_m, lo_e, trips) in rows],
        "split_dir": split_dir,
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "emit_elapsed_s": round(time.time() - t0, 1),
    }
    if split_dir:
        os.makedirs(split_dir, exist_ok=True)
        written = []
        for j, box, verd, lo_m, lo_e, trips in rows:
            for arm in ("base", "free", "full"):
                if arm == "base":
                    body_txt = (
                        f"/- TIMING MODULE arm=base leaf {j}: unfolded\n"
                        f"expression, harvested speed-lab params, plain\n"
                        f"kernel `decide` on `checkPosTMHull`. -/\n"
                        f"import Kepler.Interval.CertTM\n\n"
                        f"set_option maxHeartbeats 0\n"
                        f"set_option maxRecDepth 1000000\n\n"
                        f"namespace Kepler.Interval.Cases\n\n"
                        f"def Expr : IExpr {n} :=\n  {plan['expr']}\n\n"
                        f"def Box : Fin {n} → DInterval :=\n  {box}\n\n"
                        f"def P : TMParams := {params[j]}\n\n"
                        f"theorem leaf :\n"
                        f"    checkPosTMHull Expr Box P = "
                        f"{verdicts[j][0]} := by\n  decide\n\n"
                        f"end Kepler.Interval.Cases\n")
                elif arm == "free":
                    body_txt = (
                        f"/- TIMING MODULE arm=free leaf {j}: certificate-\n"
                        f"free fold (MVP contract, {plan_free['k']} slots),\n"
                        f"harvested speed-lab params (ps order preserved),\n"
                        f"kernel `checkPosTMHullL`. -/\n"
                        f"import Kepler.Interval.CertTM\n\n"
                        f"set_option maxHeartbeats 0\n"
                        f"set_option maxRecDepth 1000000\n\n"
                        f"namespace Kepler.Interval.Cases\n\n"
                        f"def Tbl : Fin {plan_free['k']} → IExpr {n} := "
                        f"![{plan_free['table_txt']}]\n\n"
                        f"def Body : LExpr {n} {plan_free['k']} :=\n"
                        f"  {plan_free['body']}\n\n"
                        f"def Box : Fin {n} → DInterval :=\n  {box}\n\n"
                        f"def P : TMParams := {params[j]}\n\n"
                        f"theorem leaf :\n"
                        f"    checkPosTMHullL Tbl Body Box P = "
                        f"{verdicts[j][0]} := by\n  {tactic}\n\n"
                        f"end Kepler.Interval.Cases\n")
                else:
                    body_txt = (
                        f"/- TIMING MODULE arm=full leaf {j}: FULL fold\n"
                        f"(certificate-consuming duplicates folded,\n"
                        f"{plan['k']} slots), stage-A-let probe params,\n"
                        f"kernel `checkPosTMHullL`. -/\n"
                        f"import Kepler.Interval.CertTM\n\n"
                        f"set_option maxHeartbeats 0\n"
                        f"set_option maxRecDepth 1000000\n\n"
                        f"namespace Kepler.Interval.Cases\n\n"
                        f"def Tbl : Fin {plan['k']} → IExpr {n} := "
                        f"![{plan['table_txt']}]\n\n"
                        f"def Body : LExpr {n} {plan['k']} :=\n"
                        f"  {plan['body']}\n\n"
                        f"def Box : Fin {n} → DInterval :=\n  {box}\n\n"
                        f"def P : TMParams := "
                        f"{params_lit(rung, plan['ndiv'], plan['ntrans'], trips)}\n\n"
                        f"theorem leaf :\n"
                        f"    checkPosTMHullL Tbl Body Box P = "
                        f"{'true' if verd == 'PASS' else 'false'}"
                        f" := by\n  {tactic}\n\n"
                        f"end Kepler.Interval.Cases\n")
                fp = os.path.join(split_dir, f"{mod}{arm.capitalize()}"
                                  f"{j}.lean")
                open(fp, "w").write(body_txt)
                written.append(fp)
        manifest["timing_modules"] = written
    open(out_path.rsplit(".lean", 1)[0] + ".manifest.json", "w").write(
        json.dumps(manifest, indent=1))
    print(f"[stageb-let2] wrote {out_path}  ({time.time() - t0:.1f}s)  "
          f"{len(rows)} leaves, FULL fold slots {plan['k']}, "
          f"probe PASS {n_pass}/{len(rows)}")
    if split_dir:
        print(f"[stageb-let2] {len(written)} timing modules (base/free/full "
              f"x {len(rows)} leaves) in {split_dir}")


def load_boxes(path):
    """boxes.json -> list of dyadic-pair dim tuples (emit_lean form)."""
    data = json.load(open(path))
    if len(data["boxes"]) != data.get("n", len(data["boxes"])):
        die(f"boxes.json n={data.get('n')} != {len(data['boxes'])} entries")
    return data["case"], [tuple(box_frac(iv) for iv in dim)
                          for dim in data["boxes"]]


# ---------------------------------------------------------------------------
# straddle batch pilot (production HullD2 half): pick the --hull-stats
# straddle leaves out of a sampled boxes file and batch-verify them through
# the kernel `checkPosTMHull` (= evalTMHullD2 df-hull) in <=20-leaf shard
# modules built in parallel.  An exact-rational interval evaluation of the
# ite guard polynomials per box gives the advisory root-guard census (the
# 77.6%/22.4% eligibility criterion) alongside the C-side any-guard
# straddle_hull mode.
# ---------------------------------------------------------------------------

def parse_hullstats_full(path):
    """--probe --hullstats jsonl -> {i: full line dict}."""
    rows = {}
    for ln in open(path):
        if not ln.startswith('{"i"'):
            continue
        d = json.loads(ln)
        rows[d["i"]] = d
    return rows


def iv_straddle(v):
    """True iff 0 lies in the interval (plain or sq-tagged ends)."""
    if _is_sq(v):
        return _sgn_end(v[1]) <= 0 and _sgn_end(v[2]) >= 0
    lo, hi = v
    return lo <= 0 <= hi


def guard_conds(case):
    """The ite guard cond subtrees of the hull-route expr, outermost first
    (poly+abs only for 549; anything else marks the guard unevaluable)."""
    root = parse_sexpr(hull_expr(case, 128, -80)[0])
    conds = []

    def walk(x):
        if x.op == ".ite":
            conds.append(x.kids[1])
        for k in x.kids:
            if isinstance(k, N):
                walk(k)
    walk(root)
    return conds


CONST_PAT = re.compile(r"⟨\s*(-?\d+),\s*(-?\d+)\s*⟩")


def _const_frac(x):
    m = CONST_PAT.fullmatch(" ".join(x.kids[1:]))
    if not m:
        raise ValueError(f"const token {' '.join(x.kids[1:])!r} not ⟨m, e⟩")
    from fractions import Fraction
    return Fraction(int(m.group(1))) * (Fraction(2) ** int(m.group(2)))


def _is_sq(v):
    return isinstance(v, tuple) and len(v) == 3 and v[0] == "sq"


def _sgn_end(e):
    """sign of a + s·√b for exact Fractions (b ≥ 0; √b need not be in Q)."""
    a, b, s = e
    if b < 0:
        raise ValueError("sqrt domain negative")
    if s < 0:
        if a > 0:
            return _cmp(a * a, b)
        return 0 if (a == 0 and b == 0) else -1
    if a >= 0:
        return 0 if (a == 0 and b == 0) else 1
    return _cmp(b, a * a)


def _cmp(x, y):
    return -1 if x < y else (1 if x > y else 0)


def _neg_end(e):
    return (-e[0], e[1], -e[2])


def iv_eval(x, env):
    """Exact-rational interval evaluation of a guard cond tree; env = list
    of (lo, hi) Fraction pairs per var.  Intervals are (lo, hi) Fraction
    pairs, or ("sq", e1, e2) with exact algebraic ends e = (a, b, s) =
    a + s·√b (a single sqrt is supported; anything else raises ValueError —
    callers treat the guard as unevaluable)."""
    from fractions import Fraction
    op = x.op
    if op == ".var":
        return env[int(x.kids[1])]
    if op == ".const":
        c = _const_frac(x)
        return (c, c)
    if op == ".neg":
        lo, hi = iv_eval(x.kids[1], env)
        if _is_sq(lo):
            return ("sq", _neg_end(hi[1]), _neg_end(lo[2]))
        return (-hi, -lo)
    if op == ".abs":
        lo, hi = iv_eval(x.kids[1], env)
        if _is_sq(lo):
            if _sgn_end(lo[1]) >= 0:
                return (lo, hi)
            if _sgn_end(hi[2]) <= 0:
                return ("sq", _neg_end(hi[1]), _neg_end(lo[2]))
            raise ValueError("abs of sq-interval straddling 0")
        if lo >= 0:
            return (lo, hi)
        if hi <= 0:
            return (-hi, -lo)
        return (Fraction(0), max(-lo, hi))
    if op in (".add", ".sub"):
        a = iv_eval(x.kids[1], env)
        b = iv_eval(x.kids[2], env)
        if _is_sq(a) or _is_sq(b):
            if _is_sq(a) and _is_sq(b):
                raise ValueError("sqrt ± sqrt not exact-evaluable")
            sq, r = (a, b) if _is_sq(a) else (b, a)
            if _is_sq(r):
                raise ValueError("sq ± non-rational not exact-evaluable")
            e1, e2 = sq[1], sq[2]
            if op == ".add":
                return ("sq", (e1[0] + r[0], e1[1], e1[2]),
                        (e2[0] + r[1], e2[1], e2[2]))
            return ("sq", (e1[0] - r[1], e1[1], e1[2]),
                    (e2[0] - r[0], e2[1], e2[2]))
        alo, ahi = a
        blo, bhi = b
        if op == ".add":
            return (alo + blo, ahi + bhi)
        return (alo - bhi, ahi - blo)
    if op == ".mul":
        a = iv_eval(x.kids[1], env)
        b = iv_eval(x.kids[2], env)
        if _is_sq(a) or _is_sq(b):
            raise ValueError("mul with sqrt endpoint not exact-evaluable")
        alo, ahi = a
        blo, bhi = b
        c = [alo * blo, alo * bhi, ahi * blo, ahi * bhi]
        return (min(c), max(c))
    if op == ".sqrt":
        lo, hi = iv_eval(x.kids[1], env)
        if _is_sq(lo):
            raise ValueError("nested sqrt not exact-evaluable")
        if lo < 0:
            raise ValueError("sqrt arg interval has negative part (TM would "
                             "be invalid, guard INDET)")
        return ("sq", (Fraction(0), lo, 1), (Fraction(0), hi, 1))
    raise ValueError(f"guard cond op {op} not exact-evaluable")


def cmd_pick_straddle(boxes_path, stats_path, case_path, out_prefix, cap):
    """Filter a sampled boxes file to C-side valid+closed straddle_hull
    leaves (renumbered), and record the exact-rational root-guard census
    per kept leaf (the 22.4%-census advisory criterion)."""
    t0 = time.time()
    data = json.load(open(boxes_path))
    boxes, caseid = data["boxes"], data["case"]
    stats = parse_hullstats_full(stats_path)
    if sorted(stats) != list(range(len(boxes))):
        die(f"hullstats covers {len(stats)} boxes, expected {len(boxes)}")
    case = json.load(open(case_path))
    if case["id"] != caseid:
        die(f"boxes case {caseid} != case id {case['id']}")
    conds = guard_conds(case)

    def census(box):
        env = [(Fraction(d[0]["num"], d[0]["den"]),
                Fraction(d[1]["num"], d[1]["den"])) for d in box]
        out = []
        for c in conds:
            try:
                out.append(iv_straddle(iv_eval(c, env)))
            except ValueError:
                out.append(None)
        return out

    from fractions import Fraction
    keep, drop = [], {"single": 0, "not_closed": 0, "invalid": 0,
                      "capped": 0}
    for i in range(len(boxes)):
        s = stats[i]
        if not s.get("valid"):
            drop["invalid"] += 1
        elif not s.get("closed"):
            drop["not_closed"] += 1
        elif s.get("mode") != "straddle_hull":
            drop["single"] += 1
        elif len(keep) >= cap:
            drop["capped"] += 1
        else:
            keep.append(i)
    leaves = []
    for j, i in enumerate(keep):
        s = stats[i]
        flags = census(boxes[i])
        leaves.append({"j": j, "orig_i": i, "mode": s.get("mode"),
                       "strat": s.get("strat"), "dmax": s.get("dmax"),
                       "root_straddle": flags[0] if flags else None,
                       "census": flags,
                       "f0_lo": s.get("f0", [None])[0]})
    json.dump({"case": caseid, "n": len(keep), "boxes": [boxes[i] for i in keep]},
              open(out_prefix + ".boxes.json", "w"))
    with open(out_prefix + ".hullstats.jsonl", "w") as f:
        for j, i in enumerate(keep):
            d = dict(stats[i])
            d["i"] = j
            f.write(json.dumps(d) + "\n")
    json.dump({"schema": "straddle-pick", "case": caseid,
               "source_boxes": boxes_path, "source_hullstats": stats_path,
               "sampled": len(boxes), "kept": len(keep), "dropped": drop,
               "n_guards": len(conds),
               "root_straddle_kept": sum(1 for l in leaves
                                         if l["root_straddle"]),
               "leaves": leaves},
              open(out_prefix + ".manifest.json", "w"), indent=1)
    n_root = sum(1 for l in leaves if l["root_straddle"])
    print(f"[pick-straddle] sampled {len(boxes)} -> kept {len(keep)} "
          f"straddle leaves (dropped {drop})  ({time.time() - t0:.1f}s)")
    print(f"[pick-straddle] root-guard straddle (census criterion): "
          f"{n_root}/{len(keep)};  inner-only: {len(keep) - n_root}")
    dm = {}
    for l in leaves:
        dm[l["dmax"]] = dm.get(l["dmax"], 0) + 1
    print(f"[pick-straddle] dmax histogram: {dict(sorted(dm.items()))}")


def params_sq_iv_tv(rung, ndiv, ntrans, trip):
    """TMParams component literals for one leaf (cmd_stageb pattern)."""
    _, _, g0, g1, g2, g3, g4, g5, g6 = rung
    sq = ", ".join(f"⟨{a}, {b}, {c}, ({g3}), ({g4})⟩" for a, b, c in trip)
    iv = ", ".join(f"⟨({g0}), ({g1}), ({g2})⟩" for _ in range(ndiv))
    tv = ", ".join(f"⟨({g5}), ({g6})⟩" for _ in range(ntrans))
    return f"⟨[{sq}], [{iv}], [{tv}]⟩"


def cmd_stageb_shards(case_path, boxes_path, params_path, stats_path,
                      out_dir, mod, shard_size, rung_n, tactic, compare_path):
    """Straddle batch kernel pilot: one Base module (expr), one module per
    <=shard_size-leaf group (per-leaf `checkPosTMHull ... = true|false`
    decide theorems + shard conjunction), a summary module over the shard
    theorems, and a manifest joining verdicts/loBounds/hullstats (+ an
    optional second stage-A params file, e.g. the rung-2048 arm, for the
    rung comparison).  Build: lake build <mod>S1 .. <mod>Sk <mod>Sum."""
    t0 = time.time()
    if tactic not in ("decide", "native_decide"):
        die(f"unknown tactic {tactic!r} (decide|native_decide)")
    case = json.load(open(case_path))
    cid, boxes = load_boxes(boxes_path)
    if cid != case["id"]:
        die(f"boxes case {cid} != case id {case['id']}")
    n = len(case["vars"])
    expr, nsqrt, ndiv, ntrans = hull_expr(case, rung_n, -80)
    rung, verdicts = parse_hull_params(params_path, nsqrt)
    if rung[0] != rung_n or rung[1] != -80:
        die(f"params rung {rung[0]},{rung[1]} != baked expr rung {rung_n},-80")
    if sorted(verdicts) != list(range(len(boxes))):
        die(f"params cover {sorted(verdicts)[:3]}..., expected 0..{len(boxes) - 1}")
    stats = parse_hullstats_full(stats_path)
    if sorted(stats) != list(range(len(boxes))):
        die(f"hullstats covers {len(stats)} boxes, expected {len(boxes)}")
    compare = None
    if compare_path:
        rung2, compare = parse_hull_params(compare_path, nsqrt)
        if sorted(compare) != list(range(len(boxes))):
            die(f"compare params cover {sorted(compare)[:3]}..., expected all")
        if rung2[0] == rung[0]:
            die(f"compare rung {rung2[0]} equals primary rung {rung[0]}")

    rows = []
    for k in range(len(boxes)):
        verdict, lo_m, lo_e, trip = verdicts[k]
        s = stats[k]
        if not s.get("valid") or not s.get("closed"):
            die(f"leaf {k}: C-side valid={s.get('valid')} "
                f"closed={s.get('closed')} — not a closed leaf")
        rows.append((k, boxes[k], verdict, lo_m, lo_e, trip, s))
    n_pass = sum(1 for r in rows if r[2] == "PASS")
    nshards = (len(rows) + shard_size - 1) // shard_size
    os.makedirs(out_dir, exist_ok=True)

    hdr = (f"/-\n"
           f"  549 straddle BATCH pilot (auto-generated by\n"
           f"  pipeline/interval/emit_hull_pilot.py stageb-shards).\n"
           f"  case: {case['id']}  (orig_op: {case.get('orig_op')},\n"
           f"  vars: {case['vars']})\n"
           f"  Production HullD2 half: {len(rows)} C-side straddle_hull\n"
           f"  closed leaves, kernel `checkPosTMHull` (evalTMHullD2 df-hull\n"
           f"  composite), atan rungs open ({rung_n}, -80) / closed\n"
           f"  (2048, -64).  {n_pass} PASS / {len(rows) - n_pass} NEG;\n"
           f"  NEG leaf theorems state `= false` — kernel/compiled-run\n"
           f"  AGREEMENT checks, NOT certificates.\n"
           f"  Do not edit by hand.\n"
           f"-/\n")
    base_txt = (hdr +
                "import Kepler.Interval.CertTM\n\n"
                "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
                "namespace Kepler.Interval.Cases\n\n"
                "/-- The case expression for the hull route (dummy sqrt\n"
                f"slots; atan rungs baked: open ({rung_n}, -80), closed\n"
                "(2048, -64)). -/\n"
                f"def {mod}Expr : IExpr {n} :=\n  {expr}\n\n"
                "end Kepler.Interval.Cases\n")
    base_fp = os.path.join(out_dir, f"{mod}Base.lean")
    open(base_fp, "w").write(base_txt)

    shard_names = []
    leaves_meta = []
    for si in range(nshards):
        chunk = rows[si * shard_size:(si + 1) * shard_size]
        sname = f"{mod}S{si + 1}"
        parts = []
        names = []
        for (k, box, verdict, lo_m, lo_e, trip, st) in chunk:
            j = k + 1
            tgt = "true" if verdict == "PASS" else "false"
            cmp_txt = ""
            if compare is not None:
                cv, cm, ce, _ = compare[k]
                cmp_txt = (f"; rung-{rung2[0]} arm {cv}, loBound "
                           f"{cm} * 2^({ce})")
            parts.append(
                f"/-- Straddle leaf {j} (cert leaf {st.get('orig_i', k)};"
                f" mode {st.get('mode')}, strat {st.get('strat')}, dmax"
                f" {st.get('dmax')}; C f0 lo {st.get('f0', [None])[0]});\n"
                f"stage-A margin loBound {lo_m} * 2^({lo_e}), verdict "
                f"{verdict}{cmp_txt}). -/\n"
                f"def Box{j} : Fin {n} → DInterval :=\n  {box_lit(box)}\n\n"
                f"def P{j} : TMParams := "
                f"{params_sq_iv_tv(rung, ndiv, ntrans, trip)}\n\n"
                f"theorem Leaf{j} :\n"
                f"    checkPosTMHull {mod}Expr Box{j} P{j} = {tgt} := by\n"
                f"  {tactic}\n")
            names.append((f"Leaf{j}",
                          f"checkPosTMHull {mod}Expr Box{j} P{j} = {tgt}"))
            leaves_meta.append({"j": j, "shard": si + 1,
                                "verdict": verdict, "lo_m": lo_m,
                                "lo_e": lo_e,
                                "f0_lo": st.get("f0", [None])[0],
                                "strat": st.get("strat"),
                                "dmax": st.get("dmax"),
                                "mode": st.get("mode")})
        goal = " ∧\n    ".join(p for _, p in names)
        conj = "⟨" + ", ".join(t for t, _ in names) + "⟩"
        c_pass = sum(1 for r in chunk if r[2] == "PASS")
        parts.append(
            f"/-- Shard {si + 1}: straddle leaves {chunk[0][0]}.."
            f"{chunk[-1][0]} (PASS {c_pass}, NEG {len(chunk) - c_pass});\n"
            "kernel/compiled-run agreement on every leaf; references the\n"
            "leaf theorems — no recomputation. -/\n"
            f"theorem theShard :\n    {goal} :=\n  {conj}\n\n"
            f"#print axioms theShard\n")
        shard_names.append(f"{mod}S{si + 1}")
        txt = (hdr +
               f"import Kepler.Interval.Cases.{mod}Base\n\n"
               "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
               f"namespace Kepler.Interval.Cases.{sname}\n\n"
               + "\n".join(parts) +
               f"\nend Kepler.Interval.Cases.{sname}\n")
        open(os.path.join(out_dir, f"{sname}.lean"), "w").write(txt)

    flat = []
    for si in range(nshards):
        for (k, _box, verdict, lo_m, lo_e, _trip, _st) in \
                rows[si * shard_size:(si + 1) * shard_size]:
            j = k + 1
            tgt = "true" if verdict == "PASS" else "false"
            flat.append((f"{mod}S{si + 1}.Leaf{j}",
                         f"checkPosTMHull {mod}Expr {mod}S{si + 1}.Box{j} "
                         f"{mod}S{si + 1}.P{j} = {tgt}"))
    goal = " ∧\n    ".join(p for _, p in flat)
    conj = "⟨" + ", ".join(t for t, _ in flat) + "⟩"
    sum_txt = (hdr +
               "\n".join(f"import Kepler.Interval.Cases.{s}"
                         for s in shard_names) +
               "\n\nset_option maxHeartbeats 0\n\n"
               "namespace Kepler.Interval.Cases\n\n"
               "/-- Batch summary: the full leaf-property conjunction (the\n"
               "shards state the same props; operands mirror the leaf props\n"
               "and close with the shard theorems — no recomputation). -/\n"
               f"theorem {mod}_batch :\n    {goal} :=\n  {conj}\n\n"
               f"#print axioms {mod}_batch\n\n"
               "end Kepler.Interval.Cases\n")
    open(os.path.join(out_dir, f"{mod}Sum.lean"), "w").write(sum_txt)

    manifest = {"schema": "straddle-batch", "case": case["id"],
                "out_dir": out_dir, "mod": mod, "tactic": tactic,
                "rung": [rung_n, -80], "shard": shard_size,
                "n_leaves": len(rows), "n_shards": nshards,
                "n_pass": n_pass,
                "compare_rung": rung2[0] if compare_path else None,
                "modules": [f"{mod}Base"] + shard_names + [f"{mod}Sum"],
                "leaves": leaves_meta,
                "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
                "emit_elapsed_s": round(time.time() - t0, 1)}
    open(os.path.join(out_dir, f"{mod}.manifest.json"), "w").write(
        json.dumps(manifest, indent=1))
    print(f"[stageb-shards] wrote {mod}Base + {nshards} shard modules "
          f"(<= {shard_size} leaves) + {mod}Sum  ({time.time() - t0:.1f}s)")
    print(f"[stageb-shards] {len(rows)} straddle leaves, {n_pass} PASS / "
          f"{len(rows) - n_pass} NEG (probe verdict; kernel confirms via "
          f"{tactic})")
    if compare is not None:
        c_pass = sum(1 for k in range(len(rows)) if compare[k][0] == "PASS")
        print(f"[stageb-shards] compare arm rung {rung2[0]}: {c_pass} PASS / "
              f"{len(rows) - c_pass} NEG (compiled-run probe only)")



def cmd_stagea(case_path, boxes_path, out_path, gran, rung_n, rung_out,
               mod="C549HullA200"):
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
        mod, n, expr, boxes, gran, rung_n, rung_out,
        nsqrt, ndiv, ntrans, len(boxes), meta,
        f" — SCHEMA-V3 HULLD stage A: {len(boxes)} tm leaves "
        f"(straddle batch, rung {rung_n})")
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
    elif cmd == "pick-straddle":
        cmd_pick_straddle(args[1], args[2], args[3], args[4],
                          int(opts.get("cap", 160)))
    elif cmd == "stagea":
        cmd_stagea(args[1], args[2], args[3], int(opts.get("gran", -80)),
                   int(opts.get("rung", 128)), int(opts.get("rung-out", -80)),
                   opts.get("mod", "C549HullA200"))
    elif cmd == "stageb-shards":
        cmd_stageb_shards(args[1], args[2], args[3], args[4], args[5],
                          opts.get("mod", "C549StraddleBatch"),
                          int(opts.get("shard", 20)),
                          int(opts.get("rung", 128)),
                          opts.get("tactic", "decide"),
                          opts.get("compare"))
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
    elif cmd == "stagea-let":
        cmd_stagea_let(args[1], args[2], args[3],
                       int(opts.get("leaves", 3)),
                       int(opts.get("min-size", 12)),
                       int(opts.get("max-lets", 6)),
                       int(opts.get("min-occ", 2)),
                       int(opts.get("gran", -80)),
                       int(opts.get("rung", 128)),
                       int(opts.get("rung-out", -80)))
    elif cmd == "stageb-let2":
        cmd_stageb_let2(args[1], args[2], args[3], args[4],
                        int(opts.get("leaves", 3)),
                        int(opts.get("min-size", 12)),
                        int(opts.get("max-lets", 6)),
                        int(opts.get("min-occ", 2)),
                        opts.get("tactic", "decide"),
                        opts.get("split-dir"))
    else:
        die(f"unknown subcommand {cmd}")


if __name__ == "__main__":
    main()
