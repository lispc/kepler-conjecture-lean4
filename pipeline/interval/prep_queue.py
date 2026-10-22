#!/usr/bin/env python3
"""Build the machine-readable prep re-solve queue (pipeline/interval/out/prep_queue.jsonl).

Inputs
    docs/assets/p4profile/records_classified.json   (one row per prep record)
    pipeline/interval/out/cases_prep_all/           (case JSON, if emitted)
    pipeline/interval/out/cases_prep/               (pilot case JSON set)
    pipeline/interval/out/prep_probe.jsonl          (optional bb_arb probe results)
    pipeline/interval/out/emit_all_cases.log        (optional skip reasons)

Output (one JSON object per line, sorted by route then cost)
    idv / family / line / route / class / nvars / disjuncts
    ops / ite / depth / sqrt_ops
    case_json / emit_status
    probe {status, leaves, nodes, wall_s, pending_leaves}
    leaves_known / leaf_tier / tier_source
    blockers / flags / cost_rank

Tier definition (measured leaves or static estimate):
    T0 <= 32, T1 <= 128, T2 <= 512, T3 <= 2048,
    T4 <= 8192, T5 <= 32768, T6 > 32768.
Static estimate (no probe, labeled tier_source=static):
    score = ops + 6*ite + 20*sqrt_ops.

Regression
    `--regress` checks the queue's pilot numbers against the pilot DELIVERY
    values (plain + tm leaves/nodes for the 6 R1 records), so the queue can be
    used as the cost baseline without re-reading the pilot report.

Stdlib only.
"""

import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
CLASSIFIED = os.path.join(ROOT, "docs", "assets", "p4profile",
                          "records_classified.json")
CASES_ALL = os.path.join(HERE, "out", "cases_prep_all")
CASES_PILOT = os.path.join(HERE, "out", "cases_prep")
PROBE = os.path.join(HERE, "out", "prep_probe.jsonl")
EMIT_LOG = os.path.join(HERE, "out", "emit_all_cases.log")
OUT = os.path.join(HERE, "out", "prep_queue.jsonl")

TIERS = [("T0", 32), ("T1", 128), ("T2", 512), ("T3", 2048),
         ("T4", 8192), ("T5", 32768), ("T6", None)]

ROUTE_ORDER = {"R1": 0, "R2": 1, "R3": 2, "R4": 3}

# Pilot (prep1) measured values; used for --regress and leaves_known.
PILOT = {
    "prep-2125338128": {"plain": (134539, 269077), "tm": (46099, 92197)},
    "prep-8495326405": {"plain": (48, 95), "tm": (41, 81)},
    "prep-2171548893": {"plain": (46, 91), "tm": (41, 81)},
    "prep-5550839403 delta": {"plain": (1729, 3457), "tm": (1728, 3455)},
    "prep-9368433105": {"plain": (26, 51), "tm": (26, 51)},
    "prep-5557288534 delta": {"plain": (487, 973), "tm": (487, 973)},
}


def safe_name(idv):
    return re.sub(r"[^A-Za-z0-9._-]+", "_", idv).strip("_") + ".json"


def tier_of(n):
    if n is None:
        return None, "blocked"
    for name, bound in TIERS:
        if bound is None or n <= bound:
            return name, None
    return "T6", None


def static_tier(ops, ite, sqrt_ops):
    score = (ops or 0) + 6 * (ite or 0) + 20 * (sqrt_ops or 0)
    name, _ = tier_of(score)
    return name, score


def parse_emit_log(path):
    """idv -> 'ok' | 'skip:<reason>' from the emit_rpn stdout log."""
    status = {}
    if not os.path.exists(path):
        return status
    with open(path, errors="replace") as f:
        for line in f:
            if line.startswith("EMIT "):
                m = re.match(r"EMIT\s+(\S.*?)\s+vars=", line)
                if m:
                    status[m.group(1).strip()] = "ok"
            elif line.startswith("SKIP "):
                body = line[5:].strip()
                # idv may contain spaces: reason is the last free-text run.
                for reason in ("recursion limit",):
                    if body.endswith(" " + reason):
                        status[body[:-len(reason) - 1].strip()] = \
                            "skip:" + reason
                        break
                else:
                    status[body] = "skip"
    return status


def load_cases(directory):
    """idv -> (path, stats) by matching case['id']."""
    out = {}
    if not os.path.isdir(directory):
        return out
    for fn in sorted(os.listdir(directory)):
        if not fn.endswith(".json"):
            continue
        path = os.path.join(directory, fn)
        try:
            with open(path) as f:
                case = json.load(f)
        except (ValueError, OSError):
            continue
        out[case.get("id", fn[:-5])] = (path, case.get("stats") or {})
    return out


def load_probe(path):
    """(mode, idv) -> probe record."""
    out = {}
    if not os.path.exists(path):
        return out
    with open(path, errors="replace") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except ValueError:
                continue
            out[(r.get("mode", "plain"), r["idv"])] = r
    return out


def blocker_flags(rec, emit_status, case_present):
    blockers, flags = [], []
    if rec.get("route") == "R3":
        blockers.append("route_r3_no_weapon")
    if rec.get("route") == "R4":
        blockers.append("route_r4_manual")
    if not case_present:
        blockers.append("no_case_json")
        if emit_status and emit_status.startswith("skip:"):
            blockers.append("emit_" + emit_status[5:].replace(" ", "_"))
    for app in rec.get("unknown_apps") or []:
        flags.append("unknown_app:%s" % app)
    if rec.get("disjuncts", 1) > 1:
        flags.append("disj")
    if "ite" in (rec.get("flags") or []):
        flags.append("ite")
    if "sqrt" in (rec.get("flags") or []):
        flags.append("sqrt")
    if "atnacs" in (rec.get("flags") or []):
        flags.append("atnacs")
    if rec.get("idv") == "prep-2125338128":
        blockers.append("mixed_checker_missing")
    return blockers, flags


def build():
    with open(CLASSIFIED) as f:
        records = json.load(f)
    emit_status = parse_emit_log(EMIT_LOG)
    cases_all = load_cases(CASES_ALL)
    cases_pilot = load_cases(CASES_PILOT)
    probe = load_probe(PROBE)

    rows = []
    for rec in records:
        idv = rec["idv"]
        case_path, stats = cases_all.get(idv, (None, {}))
        if case_path is None:
            case_path, stats = cases_pilot.get(idv, (None, {}))
        present = case_path is not None
        ops = stats.get("ops")
        ite = stats.get("ite")
        depth = stats.get("depth")
        sqrt_ops = None
        if present:
            try:
                with open(case_path) as f:
                    prog = json.load(f)["prog"]
                # count sqrt instructions in the RPN program
                def cnt(p):
                    k = 0
                    for ins in p:
                        if isinstance(ins, dict):
                            for key in ("cond", "then", "else"):
                                k += cnt(ins["ite"][key])
                        elif ins[0] == "sqrt":
                            k += 1
                    return k
                sqrt_ops = cnt(prog)
            except (ValueError, OSError, KeyError):
                sqrt_ops = None

        p = probe.get(("plain", idv)) or probe.get(("tm", idv))
        leaves = p.get("leaves") if p and p.get("status") == "closed" else None
        tm = probe.get(("tm", idv))
        tm_leaves = tm.get("leaves") if tm and tm.get("status") == "closed" \
            else None
        if idv in PILOT:
            leaves = PILOT[idv]["plain"][0]
            tm_leaves = PILOT[idv]["tm"][0]
            source = "pilot"
        elif leaves is not None:
            source = "measured"
        else:
            source = "static"
        if source == "static":
            tier, score = static_tier(ops, ite, sqrt_ops)
        else:
            tier, _ = tier_of(leaves)
            score = None

        blockers, flags = blocker_flags(
            rec, emit_status.get(idv), present)
        rows.append({
            "idv": idv,
            "family": rec.get("family"),
            "line": rec.get("line"),
            "route": rec.get("route"),
            "class": rec.get("class"),
            "nvars": rec.get("nvars"),
            "disjuncts": rec.get("disjuncts", 1),
            "ops": ops,
            "ite": ite,
            "depth": depth,
            "sqrt_ops": sqrt_ops,
            "case_json": os.path.relpath(case_path, ROOT) if present else None,
            "pilot_case": idv in cases_pilot,
            "emit_status": emit_status.get(idv, "unknown"),
            "probe": None if p is None else {
                "mode": p.get("mode", "plain"),
                "status": p.get("status"),
                "leaves": p.get("leaves"),
                "nodes": p.get("nodes"),
                "pending_leaves": p.get("pending_leaves"),
                "wall_s": p.get("wall_s"),
            },
            "leaves_known": leaves,
            "tm_leaves_known": tm_leaves,
            "leaf_tier": tier,
            "tier_source": source,
            "static_score": score,
            "blockers": blockers,
            "flags": flags,
        })

    route_rank = ROUTE_ORDER
    tier_rank = {name: i for i, (name, _) in enumerate(TIERS)}
    rows.sort(key=lambda r: (
        route_rank.get(r["route"], 9),
        tier_rank.get(r["leaf_tier"], 9),
        r["leaves_known"] if r["leaves_known"] is not None else 1 << 60,
        r["ops"] if r["ops"] is not None else 1 << 60,
        r["idv"]))
    for i, r in enumerate(rows, 1):
        r["cost_rank"] = i
    return rows


def regress(rows):
    by_id = {r["idv"]: r for r in rows}
    bad = []
    for idv, exp in PILOT.items():
        r = by_id.get(idv)
        if r is None:
            bad.append("%s: missing from queue" % idv)
            continue
        if (r["leaves_known"], r["tm_leaves_known"]) != \
                (exp["plain"][0], exp["tm"][0]):
            bad.append("%s: queue leaves=(%s,%s) expected=(%s,%s)"
                       % (idv, r["leaves_known"], r["tm_leaves_known"],
                          exp["plain"][0], exp["tm"][0]))
            continue
        # probe (plain) must reproduce the pilot leaves/nodes too
        p = r.get("probe")
        if p and p.get("mode") == "plain" and p.get("status") == "closed":
            if (p["leaves"], p["nodes"]) != exp["plain"]:
                bad.append("%s: probe=(%s,%s) expected=(%s,%s)"
                           % (idv, p["leaves"], p["nodes"], *exp["plain"]))
        # pilot is R1, no blockers except the known mixed-checker case
        want_block = ["mixed_checker_missing"] \
            if idv == "prep-2125338128" else []
        if sorted(r["blockers"]) != sorted(want_block):
            bad.append("%s: blockers=%s expected=%s"
                       % (idv, r["blockers"], want_block))
    for b in bad:
        print("REGRESS FAIL " + b)
    print("regression: %s (%d pilot records)"
          % ("PASS" if not bad else "FAIL", len(PILOT)))
    return 0 if not bad else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=OUT)
    ap.add_argument("--regress", action="store_true")
    args = ap.parse_args()
    rows = build()
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
    print("wrote %s (%d rows)" % (args.out, len(rows)))
    by_route = {}
    for r in rows:
        by_route.setdefault(r["route"], []).append(r)
    for route in ("R1", "R2", "R3", "R4"):
        rs = by_route.get(route, [])
        tiers = {}
        blocked = 0
        for r in rs:
            tiers[r["leaf_tier"]] = tiers.get(r["leaf_tier"], 0) + 1
            if r["blockers"]:
                blocked += 1
        print("  %s: %d records, tiers=%s, blocked=%d"
              % (route, len(rs), dict(sorted(tiers.items())), blocked))
    return regress(rows) if args.regress else 0


if __name__ == "__main__":
    sys.exit(main())
