#!/usr/bin/env python3
"""gen_data.py — regenerate a Flyspeck GMPL data section for one tame hypermap.

Faithful Python re-implementation of the OCaml chain used for the easy
certificates (see reference/flyspeck/formal_lp/glpk/):

  glpk_link.ml:      convert_to_list3 (hypermap string -> faces)
  lpproc.ml:         order_list (branch-and-bound face ordering),
                     mk_order_bb (root bb: all special sets empty),
                     std_faces / faces / card_node / card_face / triples,
                     ampl_of_bb (the data section emitter)
  build_certificates.hl: modify_hex_cases (move all 6-faces to
                     std56_flat_free before the root LP; easy build passes
                     modify_hex=true, see build_main.hl: build_all_easy)

Only the ROOT data section is generated (no branching): all apex/edge/node
sets are empty, std3_big/std3_small empty, std4_diag3 empty.  This is exactly
the LP that was solved at the root of the branch-and-bound tree; a graph
whose certificate has a single terminal was settled by this LP alone.

Usage:
  gen_data.py "HYPERMAP_STRING" > data.txt
  gen_data.py --from-dat ../path/easy_1.dat --index 1 > data.txt
"""

import argparse
import sys

sys.setrecursionlimit(2_000_000)


# ------------------------------------------------------- glpk_link.ml pieces


def convert_to_list3(s: str):
    """Hypermap string -> (id, string, faces).  Mirror of convert_to_list3:
    strip '_', first token is the id, second token (face count) is dropped,
    then repeatedly: read n, take the next n tokens as one face."""
    toks = s.replace("_", "").split()
    h, rest = toks[0], [int(t) for t in toks[1:]]
    ns = rest[1:]  # drop face count
    faces = []
    i = 0
    while i < len(ns):
        n = ns[i]
        faces.append(ns[i + 1 : i + 1 + n])
        i += 1 + n
    return h, s, faces


def rotation(xss):
    """All cyclic rotations of all lists, in order (glpk_link.ml:75)."""
    out = []
    m = max((len(x) for x in xss), default=0)
    for i in range(m):
        for xs in xss:
            if len(xs) > 0:
                out.append(xs[i % len(xs):] + xs[: i % len(xs)])
    return out


# ---------------------------------------------------------- lpproc.ml pieces


def order_list(h, xs):
    """Face ordering for branch-and-bound (lpproc.ml): hexes, quads, pents,
    tris; within a size, descending by max node occurrence count (stable)."""
    fl = [v for f in xs for v in f]
    count = {k: fl.count(k) for k in set(fl)}

    def mc(rs):
        return max((count[v] for v in rs), default=0)

    def f(k):
        group = [x for x in xs if len(x) == k]
        group.sort(key=lambda r: -mc(r))  # List.sort is stable, as is sorted
        return group

    return h, f(6) + f(4) + f(5) + f(3)


def triples(w):
    n = len(w)
    return [[w[i % n], w[(i + 1) % n], w[(i + 2) % n]] for i in range(n)]


def nub(xs):
    out = []
    for x in xs:
        if x not in out:
            out.append(x)
    return out


# ------------------------------------------------------- root bb construction


def root_bb(hypermap_string: str):
    """Root branchnbound record for the easy build (mk_order_bb +
    modify_hex_cases).  Returns dict with the fields ampl_of_bb needs."""
    h, s, ls = convert_to_list3(hypermap_string)
    h, ordered = order_list(h, ls)
    # modify_hex_cases: faces6 = filter length=6 of std_faces_not_super;
    # itlist moves each to std56_flat_free (drop1std removes the head each
    # time; hexes are at the head after order_list).  Net effect:
    faces6 = [f for f in ordered if len(f) == 6]
    return {
        "hypermap_id": h,
        "std_faces_not_super": [f for f in ordered if len(f) != 6],
        "std56_flat_free": faces6,  # prepended in reverse-iteration order == faces6 order
        "std4_diag3": [],
        "std3_big": [],
        "std3_small": [],
        "apex_sup_flat": [],
        "apex_flat": [],
        "apex_A": [],
        "apex5": [],
        "apex4": [],
        "d_edge_225_252": [],
        "d_edge_200_225": [],
        "node_218_252": [],
        "node_236_252": [],
        "node_218_236": [],
        "node_200_218": [],
    }


def std_faces(bb):
    return bb["std_faces_not_super"] + bb["std56_flat_free"] + bb["std4_diag3"]


def faces(bb):
    return (std_faces(bb) + bb["apex_sup_flat"] + bb["apex_flat"]
            + bb["apex_A"] + bb["apex5"] + bb["apex4"])


# ------------------------------------------------------------- ampl_of_bb


def ampl_of_bb(bb) -> str:
    fs = faces(bb)
    rots = rotation(fs)

    def wheremod(x):
        return rots.index(x) % len(fs)

    def wheretriplemod(x):
        # face index of the face whose rotation starts with the triple x[:3]
        return rots.index([x[0], x[1], x[2]]) % len(fs)

    def list_of(xs):
        return " ".join(str(i) for i in xs)

    def mk_faces(xs):
        return list_of([wheremod(x) for x in xs])

    def mk_dart(xs):
        return f"{xs[0]} {wheretriplemod(xs)}"

    def mk_darts(xs):
        return ", ".join(mk_dart(x) for x in xs)

    def std_face_of_size(r):
        return [i for i, f in enumerate(std_faces(bb)) if len(f) == r]

    e_dart_rows = []
    for i, f in enumerate(fs):
        e_dart_rows.append(f"(*,*,*,{i}) " + ", ".join(list_of(t) for t in triples(f)))
    e_dart = "\n".join(e_dart_rows)

    card_node = 1 + max((v for f in fs for v in f), default=-1)
    card_face = len(fs)

    return "\n".join([
        f"param card_node := {card_node};",
        f"param hypermap_id := {bb['hypermap_id']};",
        f"param card_face := {card_face};\n",
        f"set std3 := {list_of(std_face_of_size(3))};",
        f"set std4 := {list_of(std_face_of_size(4))};",
        f"set std5 := {list_of(std_face_of_size(5))};",
        f"set std6 := {list_of(std_face_of_size(6))};\n",
        f"set e_dart := \n{e_dart};\n",
        f"set std56_flat_free := {mk_faces(bb['std56_flat_free'])};",
        f"set std4_diag3 := {mk_faces(bb['std4_diag3'])};",
        f"set apex_sup_flat := {mk_darts(bb['apex_sup_flat'])};",
        f"set apex_flat := {mk_darts(bb['apex_flat'])};",
        f"set apex_A := {mk_darts(bb['apex_A'])};",
        f"set apex5 := {mk_darts(bb['apex5'])};",
        f"set apex4 := {mk_darts(bb['apex4'])};",
        f"set d_edge_225_252 := {mk_darts(bb['d_edge_225_252'])};",
        f"set d_edge_200_225 := {mk_darts(bb['d_edge_200_225'])};",
        f"set std3_big := {mk_faces(bb['std3_big'])};",
        f"set std3_small := {mk_faces(bb['std3_small'])};",
        f"set node_218_252 := {list_of(bb['node_218_252'])};",
        f"set node_236_252 := {list_of(bb['node_236_252'])};",
        f"set node_218_236 := {list_of(bb['node_218_236'])};",
        f"set node_200_218 := {list_of(bb['node_200_218'])};",
    ])


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("hypermap_string", nargs="?", default=None)
    ap.add_argument("--from-dat", default=None,
                    help="easy_*.dat certificate file (uses parse_lpcert)")
    ap.add_argument("--index", type=int, default=None,
                    help="certificate index inside --from-dat file")
    args = ap.parse_args()

    if args.from_dat is not None:
        import threading
        import parse_lpcert

        result = []

        def run():
            certs = [parse_lpcert.to_cert(v)
                     for v in parse_lpcert.to_list(parse_lpcert.read_marshal(args.from_dat))]
            result.append(certs[args.index]["hypermap_string"])

        threading.stack_size(1024 * 1024 * 1024)
        t = threading.Thread(target=run)
        t.start()
        t.join()
        s = result[0]
    elif args.hypermap_string is not None:
        s = args.hypermap_string
    else:
        ap.error("need HYPERMAP_STRING or --from-dat/--index")

    bb = root_bb(s)
    sys.stdout.write(ampl_of_bb(bb))
    return 0


if __name__ == "__main__":
    sys.exit(main())
