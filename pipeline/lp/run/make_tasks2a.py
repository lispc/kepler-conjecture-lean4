#!/usr/bin/env python3
"""make_tasks2a.py — rebuild the batch2a task list (easy multi-terminal branch LPs).

Reconstructs every branch-terminal LP of the easy Flyspeck certificates by
REPLAYING the split tree stored in easy_*.dat from the root bb, using a Python
port of the OCaml branching chain:

  lpproc.ml:         modify_bb / std_tri_prebranch / switch3 / switch4 /
                     switch5 / switch6 / split_flatq / asplit_pent
  build_certificates.hl: build (easy => hard_flag=false, so only
                     tri/quad/pent/hex splits occur; children order is the
                     switch* return order), modify_hex_cases at the root
                     (already inside gen_data.root_bb)

Terminal numbering: ti = index of the terminal in DFS order over the
certificate tree (children taken in certificate order).  Task id is
f"{hypermap_id}_t{ti:04d}"; key = easy_N (dat file number), gi = certificate
index inside that file.

Replay self-checks: at every split node the recorded split_face must equal
the face the replayed switch would branch on, and the certificate child
count must equal the switch arity (2/5/11/7).

Output: /dev/shm/lprun/batch2a_tasks.json — JSON list of
{id, graph, ti, key, gi, infeasible, data_text}
(driver.py batch2a schema; data_text = gen_data.ampl_of_bb of the terminal bb).

Usage:
  make_tasks2a.py                 # write the task file
  make_tasks2a.py --stats         # print stats only, do not write
"""

import json
import os
import sys
import threading
from pathlib import Path

REPO_LP = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_LP))
sys.setrecursionlimit(2_000_000)

import parse_lpcert as P  # noqa: E402
import gen_data  # noqa: E402

BIN = Path(os.environ.get(
    "LPBIN", "/dev/shm/kepler-ref/flyspeck/formal_lp/glpk/binary"))
OUT = Path(os.environ.get("LPRUN_ROOT", "/dev/shm/lprun")) / "batch2a_tasks.json"

# ---------------------------------------------------------------- lpproc port
# bb is the dict shape produced by gen_data.root_bb.  Faces are node lists;
# dart-ish entries (apex_*, d_edge_*) are int lists whose head is the special
# dart's node.  modify_bb never mutates its input.


def get_values(key, xs):
    return [v for k, v in xs if k == key]


# modify_bb field keys -> bb dict keys.  The "jq" jump-queue is a no-op for
# the fields the switches use (no "jq" keys ever passed).
_FIELD_MAP = {
    "bt": "std3_big",
    "st": "std3_small",
    "flat_free": "std56_flat_free",
    "diag3": "std4_diag3",
    "ff": "apex_flat",
    "sf": "apex_sup_flat",
    "af": "apex_A",
    "apex4": "apex4",
    "apex5": "apex5",
    "e_225_252": "d_edge_225_252",
    "e_200_225": "d_edge_200_225",
}

# vfield keys (node bound lists; used by the hard-cases node numerics and
# switch_node) -> bb dict keys.
_VFIELD_MAP = {
    "218_252": "node_218_252",
    "236_252": "node_236_252",
    "218_236": "node_218_236",
    "200_218": "node_200_218",
}


def modify_bb(bb, drop1std, fields, vfields=()):
    """lpproc.ml:219 modify_bb, specialized to drop1std/fields/vfields as used
    by switch3..6, switch_std3/edge/node and the hard numerics (no "jq"
    fields).  add key xs t = nub(vals @ t)."""
    out = dict(bb)
    std = bb["std_faces_not_super"]
    if drop1std:
        out["std_faces_not_super"] = std[1:]
    # else: jump_queue "jq" [] std == nub(std) == std (faces are distinct)
    for key, dest in _FIELD_MAP.items():
        vals = get_values(key, fields)
        if vals:
            out[dest] = gen_data.nub(vals + bb[dest])
    for key, dest in _VFIELD_MAP.items():
        vals = get_values(key, vfields)
        if vals:
            out[dest] = gen_data.nub(vals + bb[dest])
    return out


def rotL(i, xs):
    """glpk_link.ml rotateL (handles negative i like OCaml's signed mod:
    rotateL i xs rotates left by i mod n)."""
    n = len(xs)
    i %= n
    return xs[i:] + xs[:i]


def split_flatq(xs, i):
    """lpproc.ml:386 — {y1,y3} is the new diagonal."""
    r = rotL(i, xs)
    y1, y2, y3, ys = r[0], r[1], r[2], r[3:]
    return [y2, y3, y1], rotL(-1, [y1, y3] + ys)


def asplit_pent(xs, i):
    """lpproc.ml:391 — y2,y4 darts of flat; y3 the point of the A."""
    y1, y2, y3, y4, y5 = rotL(i, xs)
    return [y2, y3, y1], [y3, y5, y1], [y4, y5, y3]


def std_tri_prebranch(bb):
    """lpproc.ml:268."""
    r = gen_data.rotation(bb["std3_big"] + bb["std3_small"])
    return [t for t in bb["std_faces_not_super"]
            if len(t) == 3 and t not in r]


def switch3(bb):
    """lpproc.ml:396 — returns (split_face, [big, small])."""
    pre = std_tri_prebranch(bb)
    if not pre:
        raise ValueError("switch3 empty " + bb["hypermap_id"])
    fc = pre[0]
    return fc, [modify_bb(bb, False, [("bt", fc)]),
                modify_bb(bb, False, [("st", fc)])]


def switch4(bb):
    """lpproc.ml:400 — [ff0, ff1, sf0, sf1, diag3]."""
    std = bb["std_faces_not_super"]
    if not std:
        raise ValueError("switch4 empty " + bb["hypermap_id"])
    fc = std[0]

    def f(s, i):
        a, b = split_flatq(fc, i)
        return modify_bb(bb, True, [(s, a), (s, b)])
    return fc, [f("ff", 0), f("ff", 1), f("sf", 0), f("sf", 1),
                modify_bb(bb, True, [("diag3", fc)])]


def switch5(bb):
    """lpproc.ml:408 — flat_free, then 5 apex4, then 5 apex_A (11 total)."""
    std = bb["std_faces_not_super"]
    if not std:
        raise ValueError("switch5 empty " + bb["hypermap_id"])
    fc = std[0]
    bbs = []
    for i in range(5):
        a, b = split_flatq(fc, i)
        bbs.append(modify_bb(bb, True, [("ff", a), ("apex4", b)]))
    ccs = []
    for i in range(5):
        a, b, c = asplit_pent(fc, i)
        ccs.append(modify_bb(bb, True, [("ff", a), ("af", b), ("ff", c)]))
    return fc, [modify_bb(bb, True, [("flat_free", fc)])] + bbs + ccs


def switch6(bb):
    """lpproc.ml:419 — flat_free, then 6 apex5 (7 total)."""
    std = bb["std_faces_not_super"]
    if not std:
        raise ValueError("switch6 empty " + bb["hypermap_id"])
    fc = std[0]
    bbs = []
    for i in range(6):
        a, b = split_flatq(fc, i)
        bbs.append(modify_bb(bb, True, [("ff", a), ("apex5", b)]))
    return fc, [modify_bb(bb, True, [("flat_free", fc)])] + bbs


SWITCH = {"tri": switch3, "quad": switch4, "pent": switch5, "hex": switch6}


# ------------------------------------------------------------- tree replay


def walk_terminals(root_case, bb):
    """DFS over the certificate tree, children in certificate order.
    Yields (bb_at_terminal, infeasible) for each Lp_terminal leaf."""
    if root_case[1] == 0:  # Lp_terminal
        t = root_case[2][0][2]
        yield bb, bool(t[1])
        return
    assert root_case[1] == 1, f"bad case tag {root_case[1]}"
    sc = root_case[2][0][2]
    stype, sface = sc[0], P.to_list(sc[1])
    children = P.to_list(root_case[2][1])
    fc, bbs = SWITCH[stype](bb)
    if sface != fc:
        raise ValueError(
            f"split_face mismatch: certificate {sface} vs replay {fc} "
            f"({stype} split, graph {bb['hypermap_id']})")
    if len(children) != len(bbs):
        raise ValueError(
            f"child count mismatch: certificate {len(children)} vs "
            f"switch {len(bbs)} ({stype} split, graph {bb['hypermap_id']})")
    for ch, bb2 in zip(children, bbs):
        yield from walk_terminals(ch, bb2)


def build_tasks():
    tasks = []
    n_files = 0
    for n in range(1, 1000):
        path = BIN / f"easy_{n}.dat"
        if not path.exists():
            break
        n_files += 1
        certs = [P.to_cert(v) for v in P.to_list(P.read_marshal(str(path)))]
        for gi, c in enumerate(certs):
            nt, _ni = P.terminal_info(c["root_case"])
            if nt == 1:
                continue  # batch1 (root LP) territory
            root = gen_data.root_bb(c["hypermap_string"])
            graph = root["hypermap_id"]
            for ti, (bb, infeasible) in enumerate(
                    walk_terminals(c["root_case"], root)):
                tasks.append({
                    "id": f"{graph}_t{ti:04d}",
                    "graph": graph,
                    "ti": ti,
                    "key": f"easy_{n}",
                    "gi": gi,
                    "infeasible": infeasible,
                    "data_text": gen_data.ampl_of_bb(bb),
                })
    return tasks, n_files


def main():
    stats_only = "--stats" in sys.argv
    tasks, n_files = build_tasks()
    n_inf = sum(1 for t in tasks if t["infeasible"])
    graphs = {t["graph"] for t in tasks}
    ids = [t["id"] for t in tasks]
    assert len(set(ids)) == len(ids), "duplicate task ids"
    print(f"[make_tasks2a] {n_files} easy files, {len(graphs)} multi-terminal "
          f"graphs, {len(tasks)} terminal tasks, {n_inf} infeasible")
    if not stats_only:
        OUT.write_text(json.dumps(tasks))
        print(f"[make_tasks2a] wrote {OUT} ({OUT.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    # Marshal cons-lists nest deeply; run with a large stack (as parse_lpcert).
    result = []

    def run():
        result.append(main())

    threading.stack_size(1024 * 1024 * 1024)
    t = threading.Thread(target=run)
    t.start()
    t.join()
    sys.exit(result[0])
