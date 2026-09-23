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
        mm.close()
    json.dump({"case": "5490182221", "n": len(picks), "boxes": picks},
              open(boxes_path, "w"))
    json.dump({"schema": "hull-pilot-200", "case": "5490182221",
               "k": k, "stride": stride, "n_total": n_total,
               "n_tm": n_tm, "picked_leaf_indices": picked_idx},
              open(manifest_path, "w"), indent=1)
    dt = time.time() - t0
    print(f"[sample] leaves {n_total}  tm {n_tm}  stride {stride}  "
          f"picked {len(picks)}  ({dt:.1f}s)  -> {boxes_path}")
    print(f"[sample] picked cert leaf indices 0..{picked_idx[-1]} "
          f"(first {picked_idx[:3]} ... last {picked_idx[-3:]})")


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
    else:
        die(f"unknown subcommand {cmd}")


if __name__ == "__main__":
    main()
