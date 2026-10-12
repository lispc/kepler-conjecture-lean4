#!/usr/bin/env python3
"""gen_branch.py — regenerate a Flyspeck GMPL data section for a BRANCH
(non-root) terminal of a tame hypermap's branch-and-bound tree.

This extends gen_data.py (root-only) with the branch machinery that the
README "未做" note lists: the rebuild of `modify_bb` / `switch3` / `switch4` /
`switch5` / `switch6` (reference/flyspeck/formal_lp/glpk/lpproc.ml) plus the
hard-case additions `switch_std3` / `switch_edge` / `switch_node` /
`set_face_numerics` / `set_node_numerics` (glpk/hard_lp.ml +
glpk/build_certificates.hl:178-233).

Reconstruction model (mirrors build_certificates.hl `build`, the generator of
the binary certificates): the certificate tree records, at every split node,
the split_type string and the split_face that `build` branched on.  Walking
the tree depth-first from the root and applying, at each node, the child
branch selected by the child index reproduces the exact `branchnbound` record
at every terminal; `ampl_of_bb` (reused from gen_data) then emits its data
section, which is byte-equivalent in meaning to what glpsol consumed at that
terminal when LP-HL.exe built the certificate.

Branch tables (all verified against lpproc.ml:396-424 / hard_lp.ml:296-306):

  type   children (in order)                                drop1std
  tri    [bt face, st face]                                 false
  quad   [ff a0 ff b0, ff a1 ff b1, sf a0 sf b1, sf a1 sf b0,
         diag3 face]                                        true
  pent   [flat_free face] + 5x[ff a, apex4 b] + 5x[ff a, af b, ff c]   true
  hex    [flat_free face] + 6x[ff a, apex5 b]                true
  edge   [e_225_252 dart, e_200_225 dart]                    false
  218    [218_252 i, 200_218 i]  (i not highish)             false
  236    [218_236 i, 236_252 i]  (i highish)                 false

add_big / mid / high are NOT free-standing branch operations: build
(build_certificates.hl:225-233, hard build only) applies set_face_numerics
then set_node_numerics at EVERY step, and the recorded single-child wrapper
nodes are exactly the non-empty info lists of that step.  A firing whose
resulting dart list is empty still modifies the bb but leaves no wrapper
(validated empirically on hard_1 terminal 4: e_225_252 2->4 with zero
infos, LP 12.0013 -> 11.9894).  Hence --mode hard runs the per-step
numerics and consumes the recorded wrappers against them; --mode easy
(build_all_easy, hard_flag=false) never runs them.  117/117 sampled hard
terminals across hard_1/2/10/11/15 then reproduce LP values <= 11.9999
consistent with their certificates (glpsol 5.0 float + SoPlex exact).

Mode inference: easy_*.dat -> easy, hard_*.dat -> hard (--mode to override).

Usage:
  gen_branch.py --from-dat FILE.dat --index I --leaf K          # leaf K data section
  gen_branch.py --from-dat FILE.dat --index I --leaves 0,1,2 --out-dir DIR
  gen_branch.py --from-dat FILE.dat --index I --trace --leaf 0  # bb chain on stderr
  gen_branch.py --from-dat FILE.dat --index I --census          # split-type histogram
"""

import argparse
import sys

sys.setrecursionlimit(2_000_000)

sys.path.insert(0, __file__.rsplit("/", 1)[0] or ".")
import gen_data  # noqa: E402  (convert_to_list3 / order_list / rotation / ampl_of_bb)


# ------------------------------------------------------------- list helpers
# (semantics verified against glpk_link.ml:65-103 and general/lib.hl)


def rotate_l(i, xs):
    """OCaml rotateL: left rotation by i (mod n), i >= 0."""
    n = len(xs)
    if n == 0:
        return []
    i %= n
    return xs[i:] + xs[:i]


def rotate_r(i, xs):
    """OCaml rotateR i = rotateL (-i): right rotation by i."""
    n = len(xs)
    if n == 0:
        return []
    return rotate_l(n - (i % n), xs)


def split_flatq(xs, i):
    """lpproc.ml:386 — {y1,y3} is the new diagonal of flat quad fc."""
    y1, y2, y3, ys = (lambda t: (t[0], t[1], t[2], t[3:]))(rotate_l(i, xs))
    # rotateR 1 (y1::y3::ys)
    return [y2, y3, y1], [ys[-1], y1, y3] + ys[:-1]


def asplit_pent(xs, i):
    """lpproc.ml:391 — y2,y4 darts of flat; y3 is the point of the A."""
    y1, y2, y3, y4, y5 = rotate_l(i, xs)
    return [y2, y3, y1], [y3, y5, y1], [y4, y5, y3]


def subtract(l1, l2):
    return [x for x in l1 if x not in l2]


def intersect(l1, l2):
    return [x for x in l1 if x in l2]


def unions(lists):
    """lib.hl unions = itlist union = first-occurrence order of the concat."""
    out = []
    for xs in lists:
        for x in xs:
            if x not in out:
                out.append(x)
    return out


def nub(xs):
    out = []
    for x in xs:
        if x not in out:
            out.append(x)
    return out


# ------------------------------------------------------------ modify_bb


def modify_bb(bb, drop1std, fields, vfields):
    """lpproc.ml:219 — faithful port (field keys = OCaml strings)."""
    def gv(key, pairs):
        return [v for (k, v) in pairs if k == key]

    def add(key, pairs, t):
        return nub(gv(key, pairs) + t)

    std = bb["std_faces_not_super"]
    if drop1std:
        new_std = std[1:]
    else:  # jump_queue_std: keep "jq" values, drop old entries rotated by them
        ys = gv("jq", fields)
        e = gen_data.rotation(ys) if ys else []
        new_std = nub(ys + [t for t in std if t not in e])
    return {
        "hypermap_id": bb["hypermap_id"],
        "std_faces_not_super": new_std,
        "std3_big": add("bt", fields, bb["std3_big"]),
        "std3_small": add("st", fields, bb["std3_small"]),
        "std56_flat_free": add("flat_free", fields, bb["std56_flat_free"]),
        "std4_diag3": add("diag3", fields, bb["std4_diag3"]),
        "apex_flat": add("ff", fields, bb["apex_flat"]),
        "apex_sup_flat": add("sf", fields, bb["apex_sup_flat"]),
        "apex_A": add("af", fields, bb["apex_A"]),
        "apex4": add("apex4", fields, bb["apex4"]),
        "apex5": add("apex5", fields, bb["apex5"]),
        "d_edge_225_252": add("e_225_252", fields, bb["d_edge_225_252"]),
        "d_edge_200_225": add("e_200_225", fields, bb["d_edge_200_225"]),
        "node_218_252": add("218_252", vfields, bb["node_218_252"]),
        "node_236_252": add("236_252", vfields, bb["node_236_252"]),
        "node_218_236": add("218_236", vfields, bb["node_218_236"]),
        "node_200_218": add("200_218", vfields, bb["node_200_218"]),
    }


# ------------------------------------------------------- faces machinery


def std_faces(bb):
    return bb["std_faces_not_super"] + bb["std56_flat_free"] + bb["std4_diag3"]


def faces(bb):
    return (std_faces(bb) + bb["apex_sup_flat"] + bb["apex_flat"]
            + bb["apex_A"] + bb["apex5"] + bb["apex4"])


def card_node(bb):
    return 1 + max((v for f in faces(bb) for v in f), default=-1)


def std_tri_prebranch(bb):
    """lpproc.ml:268 — std triangles not already big/small."""
    r = gen_data.rotation(bb["std3_big"] + bb["std3_small"])
    return [t for t in bb["std_faces_not_super"] if len(t) == 3 and t not in r]


def face_of_dart(dart, bb):
    """hard_lp.ml:153 — first face whose triples contain dart; returns its
    leading triple (== the face itself for triangles)."""
    for f in faces(bb):
        ts = gen_data.triples(f)
        if dart in ts:
            return ts[0]
    raise ValueError(f"face_of_dart: dart {dart} not found")


def opposite_edge(dart, bb):
    """hard_lp.ml:247 — [j;i;k'] with k' from the face entering at i via j."""
    i, j = dart[0], dart[1]
    for f in gen_data.rotation(faces(bb)):
        if f[0] == j and f[1] == i:
            return [j, i, f[2]]
    raise ValueError(f"opposite_edge: dart {dart} not found")


def highish(bb):
    """hard_lp.ml:151."""
    excl = bb["node_218_236"] + bb["node_236_252"]
    return [x for x in bb["node_218_252"] if x not in excl]


# ------------------------------------------------------------- switches


def switch3(bb):
    """lpproc.ml:396 — easy tri: head of std_tri_prebranch."""
    pre = std_tri_prebranch(bb)
    if not pre:
        raise ValueError("switch3 empty " + bb["hypermap_id"])
    fc = pre[0]
    return [modify_bb(bb, False, [("bt", fc)], []),
            modify_bb(bb, False, [("st", fc)], [])]


def switch4(bb):
    """lpproc.ml:400 — [ff 0, ff 1, sf 0, sf 1, diag3]."""
    std = bb["std_faces_not_super"]
    if not std:
        raise ValueError("switch4 empty " + bb["hypermap_id"])
    fc = std[0]

    def mo(s, a, b):
        return modify_bb(bb, True, [(s, a), (s, b)], [])

    out = []
    for s in ("ff", "sf"):
        for i in (0, 1):
            a, b = split_flatq(fc, i)
            out.append(mo(s, a, b))
    out.append(modify_bb(bb, True, [("diag3", fc)], []))
    return out


def switch5(bb):
    """lpproc.ml:408 — [flat_free] + 5x[ff,apex4] + 5x[ff,af,ff]."""
    std = bb["std_faces_not_super"]
    if not std:
        raise ValueError("switch5 empty " + bb["hypermap_id"])
    fc = std[0]
    out = [modify_bb(bb, True, [("flat_free", fc)], [])]
    for i in range(5):
        a, b = split_flatq(fc, i)
        out.append(modify_bb(bb, True, [("ff", a), ("apex4", b)], []))
    for i in range(5):
        a, b, c = asplit_pent(fc, i)
        out.append(modify_bb(bb, True, [("ff", a), ("af", b), ("ff", c)], []))
    return out


def switch6(bb):
    """lpproc.ml:419 — [flat_free] + 6x[ff,apex5]."""
    std = bb["std_faces_not_super"]
    if not std:
        raise ValueError("switch6 empty " + bb["hypermap_id"])
    fc = std[0]
    out = [modify_bb(bb, True, [("flat_free", fc)], [])]
    for i in range(6):
        a, b = split_flatq(fc, i)
        out.append(modify_bb(bb, True, [("ff", a), ("apex5", b)], []))
    return out


def switch_std3(bb, c):
    """hard_lp.ml:296 — c is a face (the certificate's split_face)."""
    return [modify_bb(bb, False, [("bt", c)], []),
            modify_bb(bb, False, [("st", c)], [])]


def switch_edge(bb, d):
    """hard_lp.ml:300 — d is a dart (3-element rotation of a triangle)."""
    return [modify_bb(bb, False, [("e_225_252", d)], []),
            modify_bb(bb, False, [("e_200_225", d)], [])]


def switch_node(bb, i):
    """hard_lp.ml:303 — high/low node split."""
    if i in highish(bb):
        return [modify_bb(bb, False, [], [("218_236", i)]),
                modify_bb(bb, False, [], [("236_252", i)])]
    nodelist = list(range(card_node(bb)))
    settable = subtract(nodelist, bb["node_200_218"] + bb["node_218_236"]
                        + bb["node_236_252"])
    if i not in settable:
        raise ValueError(f"switch_node: node {i} not settable")
    return [modify_bb(bb, False, [], [("218_252", i)]),
            modify_bb(bb, False, [], [("200_218", i)])]


# ------------------------------------------- hard numerics (single-child)


def set_face_numerics_info(bb):
    """build_certificates.hl:178 — returns (new_bb, [add_big info darts])."""
    opp = lambda xs: nub(xs + [opposite_edge(d, bb) for d in xs])
    edge_of_small = opp(gen_data.rotation(bb["std3_small"]))
    short_edge = opp(bb["d_edge_200_225"])
    long_edge = opp(bb["d_edge_225_252"])
    if intersect(edge_of_small, long_edge):
        raise ValueError("set_face_numerics: small/long edge clash")
    shortadds = subtract(edge_of_small + short_edge, bb["d_edge_200_225"])
    shortfields = [("e_200_225", t) for t in shortadds]
    longadds = subtract(long_edge, bb["d_edge_225_252"])
    longfields = [("e_225_252", t) for t in longadds]
    r = [t for t in nub([face_of_dart(d, bb) for d in long_edge])
         if t in std_faces(bb) and len(t) == 3]
    if intersect(gen_data.rotation(bb["std3_small"]), r):
        raise ValueError("set_face_numerics: small/big clash")
    bigfields = [("bt", t) for t in subtract(r, bb["std3_big"])]
    fields = shortfields + longfields + bigfields
    if not fields:
        return bb, []
    new_bb = modify_bb(bb, False, fields, [])
    new_big_faces = subtract(r, bb["std3_big"])
    long_edge_faces = list(zip([face_of_dart(d, bb) for d in long_edge],
                               long_edge))
    darts = []
    for f in new_big_faces:
        for (k, v) in long_edge_faces:
            if k == f:
                darts.append(v)
                break
        else:
            raise ValueError("set_face_numerics: assoc miss")
    return new_bb, [{"split_type": "add_big", "split_face": d} for d in darts]


def set_node_numerics_info(bb):
    """build_certificates.hl:204 — returns (new_bb, [mid/high info])."""
    if card_node(bb) != 13:
        return bb, []
    n_high = len(bb["node_236_252"])
    n_mid = len(bb["node_218_236"])
    n_highish = len(highish(bb))
    if n_high == 0 and n_mid + n_highish < 2:
        return bb, []
    if n_mid * 18 + n_highish * 18 + n_high * 36 > 52:
        raise ValueError("set_node_numerics: budget")
    node_new_low = subtract(list(range(card_node(bb))),
                            unions([bb["node_200_218"], bb["node_218_236"],
                                    bb["node_236_252"], bb["node_218_252"]]))
    vfields_low = [("200_218", t) for t in node_new_low]
    vfields_mid = [("218_236", t) for t in highish(bb)]
    vfields = vfields_low + vfields_mid
    if not vfields:
        return bb, []
    new_bb = modify_bb(bb, False, [], vfields)
    if n_high > 0:
        info = {"split_type": "high", "split_face": list(bb["node_236_252"])}
    else:
        info = {"split_type": "mid",
                "split_face": list(bb["node_218_236"] + highish(bb))}
    return new_bb, [info]


# --------------------------------------------------------- root + walker


def root_bb(hypermap_string):
    """mk_order_bb + modify_hex_cases (both easy and hard builds pass
    modify_hex=true, build_main.hl:62/69)."""
    return gen_data.root_bb(hypermap_string)


def decode_case(case):
    """parse_lpcert block -> ("terminal", None) | ("split", type, face, kids)."""
    import parse_lpcert as P
    if case[1] == 0:
        return ("terminal",)
    sc = case[2][0][2]
    return ("split", sc[0], P.to_list(sc[1]), P.to_list(case[2][1]))


def apply_branch(bb, stype, sface, idx, trace, depth):
    """One split node: assert the recorded split_face against the reconstructed
    bb, then return child number `idx` of the corresponding switch."""

    def note(msg):
        if trace:
            print(f"  {'  ' * depth}{stype} face={sface} -> child {idx}: {msg}",
                  file=sys.stderr)

    if stype in ("quad", "pent", "hex"):
        head = bb["std_faces_not_super"][0]
        if sface != head:
            raise AssertionError(
                f"{stype}: recorded split_face {sface} != bb head {head}")
        bbs = {"quad": switch4, "pent": switch5, "hex": switch6}[stype](bb)
        note(f"{len(bbs)} branches, head face {head}")
        return bbs[idx]

    if stype == "tri":
        pre = std_tri_prebranch(bb)
        if pre and pre[0] == sface:
            note("easy tri (head of std_tri_prebranch)")
        elif sface in faces(bb) and len(sface) == 3:
            note("hard tri (recorded face)")
        else:
            raise AssertionError(f"tri: split_face {sface} is not a face")
        return switch_std3(bb, sface)[idx]

    if stype == "edge":
        face_of_dart(sface, bb)  # assertion: dart belongs to some face
        note("hard edge split")
        return switch_edge(bb, sface)[idx]

    if stype in ("218", "236"):
        if len(sface) != 1:
            raise AssertionError(f"{stype}: split_face {sface} not a singleton")
        i = sface[0]
        hi = highish(bb)
        if stype == "236":
            if i not in hi:
                raise AssertionError(f"236: node {i} not highish")
        else:
            settable = subtract(range(card_node(bb)),
                                bb["node_200_218"] + bb["node_218_236"]
                                + bb["node_236_252"])
            if i not in settable:
                raise AssertionError(f"218: node {i} not settable")
        note(f"node {i} ({stype})")
        return switch_node(bb, i)[idx]

    raise ValueError(f"unknown split_type {stype!r}")


def hard_numerics(bb, pending, trace, depth):
    """build (build_certificates.hl:225-233) applies set_face_numerics_info
    then set_node_numerics_info at EVERY hard build step; the recorded
    add_big/mid/high wrapper nodes are exactly the non-empty info lists of
    that step (a firing with an empty dart list silently modifies the bb and
    leaves no wrapper — validated on hard_1 terminal 4).  `pending` carries
    the still-unconsumed infos of the current step across the wrapper chain.
    Returns (bb, pending)."""
    if pending:
        return bb, pending
    bb1, list1 = set_face_numerics_info(bb)
    bb2, list2 = set_node_numerics_info(bb1)
    if trace and (list1 or list2):
        print(f"  {'  ' * depth}numerics fire: "
              + ", ".join(i["split_type"] for i in list1 + list2),
              file=sys.stderr)
    return bb2, list1 + list2


def consume_wrapper(bb, stype, sface, pending, trace, depth):
    """Consume one recorded wrapper node against the step's pending infos."""
    if not pending:
        raise AssertionError(f"{stype}: wrapper node but no pending info")
    exp = pending[0]
    if exp["split_type"] != stype or exp["split_face"] != sface:
        raise AssertionError(
            f"{stype}: recorded {sface} != recomputed {exp['split_face']}")
    if trace:
        print(f"  {'  ' * depth}{stype} face={sface} -> wrapper "
              f"({len(pending) - 1} pending)", file=sys.stderr)
    return pending[1:]


def walk_leaf(root_case, bb0, target_ti, trace=False, mode="easy"):
    """DFS to terminal `target_ti` (same order as LPSchema.dfsTerminals).
    Returns (bb_at_leaf, path) where path lists (type, face, child_index).
    mode="hard" applies the per-step numerics of build_certificates.build."""
    counter = [0]
    result = {}

    def rec(case, bb, depth, path, pending):
        kind = decode_case(case)
        if kind[0] == "terminal":
            if mode == "hard":
                bb, pending = hard_numerics(bb, pending, trace, depth)
                if pending:
                    raise AssertionError(
                        "terminal step left unconsumed numerics infos")
            if counter[0] == target_ti:
                result["bb"] = bb
                result["path"] = path
            counter[0] += 1
            return
        _, stype, sface, kids = kind
        if mode == "hard":
            bb, pending = hard_numerics(bb, pending, trace, depth)
        for idx, child in enumerate(kids):
            if "bb" in result:
                return
            if stype in ("add_big", "mid", "high"):
                pending2 = consume_wrapper(bb, stype, sface, pending,
                                           trace, depth)
                rec(child, bb, depth + 1, path + [(stype, sface, idx)],
                    pending2)
            else:
                if pending:
                    raise AssertionError(
                        f"{stype}: split node with unconsumed numerics infos")
                bb2 = apply_branch(bb, stype, sface, idx, trace, depth)
                rec(child, bb2, depth + 1, path + [(stype, sface, idx)], [])

    rec(root_case, dict(bb0), 0, [], [])
    if "bb" not in result:
        raise ValueError(f"terminal {target_ti} out of range "
                         f"(tree has {counter[0]})")
    return result["bb"], result["path"]


def census(root_case):
    """Split-type histogram + terminal/infeasible counts of the whole tree."""
    import parse_lpcert as P
    hist = {}
    terms = [0]

    def rec(case):
        kind = decode_case(case)
        if kind[0] == "terminal":
            terms[0] += 1
            return
        _, stype, _, kids = kind
        hist[stype] = hist.get(stype, 0) + 1
        for c in kids:
            rec(c)

    rec(root_case)
    return hist, terms[0]


# ------------------------------------------------------------------ main


def load_cert(dat, index):
    import threading
    import parse_lpcert as P
    result = []

    def run():
        certs = [P.to_cert(v)
                 for v in P.to_list(P.read_marshal(dat))]
        result.append(certs[index])

    threading.stack_size(1024 * 1024 * 1024)
    t = threading.Thread(target=run)
    t.start()
    t.join()
    return result[0]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--from-dat", required=True)
    ap.add_argument("--index", type=int, required=True)
    tgt = ap.add_mutually_exclusive_group(required=True)
    tgt.add_argument("--leaf", type=int)
    tgt.add_argument("--leaves", default=None)
    tgt.add_argument("--census", action="store_true")
    ap.add_argument("--out-dir", default=None,
                    help="write leaf<i>_data.txt here (multi-leaf mode)")
    ap.add_argument("--trace", action="store_true",
                    help="bb chain summary on stderr")
    ap.add_argument("--mode", choices=("easy", "hard", "auto"), default="auto",
                    help="build mode: easy = build_all_easy (no per-step "
                         "numerics); hard = build_all_hard (per-step "
                         "set_face/node_numerics, build_certificates.hl:229). "
                         "auto infers from the .dat filename.")
    args = ap.parse_args()

    mode = args.mode
    if mode == "auto":
        import os
        base = os.path.basename(args.from_dat)
        mode = "hard" if base.startswith("hard") else "easy"
        if args.trace:
            print(f"[mode] auto -> {mode}", file=sys.stderr)

    cert = load_cert(args.from_dat, args.index)
    hs = cert["hypermap_string"]
    hid = hs.replace("_", "").split()[0]

    if args.census:
        hist, n = census(cert["root_case"])
        print(f"{hid}: {n} terminals; splits: "
              + ", ".join(f"{k}x{v}" for k, v in sorted(hist.items())))
        return 0

    bb0 = root_bb(hs)
    leaves = [args.leaf] if args.leaf is not None else \
        [int(x) for x in args.leaves.split(",")]

    outputs = []
    for k in leaves:
        bb, path = walk_leaf(cert["root_case"], bb0, k, trace=args.trace,
                             mode=mode)
        if args.trace:
            print(f"[{hid}] leaf {k}: path "
                  + " -> ".join(f"{t}#{i}" for (t, _, i) in path), file=sys.stderr)
            print(f"[{hid}] leaf {k}: faces={len(faces(bb))} "
                  f"std={len(bb['std_faces_not_super'])} "
                  f"ff={len(bb['std56_flat_free'])} "
                  f"diag3={len(bb['std4_diag3'])} "
                  f"sf={len(bb['apex_sup_flat'])} "
                  f"ffx={len(bb['apex_flat'])} "
                  f"af={len(bb['apex_A'])} "
                  f"apex4={len(bb['apex4'])} apex5={len(bb['apex5'])} "
                  f"e225={len(bb['d_edge_225_252'])} "
                  f"e200={len(bb['d_edge_200_225'])} "
                  f"n218_252={len(bb['node_218_252'])} "
                  f"n236_252={len(bb['node_236_252'])} "
                  f"n218_236={len(bb['node_218_236'])} "
                  f"n200_218={len(bb['node_200_218'])}", file=sys.stderr)
        outputs.append((k, gen_data.ampl_of_bb(bb)))

    if args.out_dir:
        import pathlib
        out = pathlib.Path(args.out_dir)
        out.mkdir(parents=True, exist_ok=True)
        for k, txt in outputs:
            (out / f"leaf{k}_data.txt").write_text(txt + "\n")
            print(f"{out / f'leaf{k}_data.txt'}")
    else:
        sys.stdout.write(outputs[0][1] + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
