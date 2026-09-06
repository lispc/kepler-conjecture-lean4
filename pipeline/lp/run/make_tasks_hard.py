#!/usr/bin/env python3
"""make_tasks_hard.py — split-tree replay for the HARD Flyspeck certificates
(hard_*.dat), hard_1 deviation experiment, and the hard task list.

Hard trees differ from easy ones (build_certificates.hl `build` with
hard_flag=true — which is every node of a hard tree, since the flag is
threaded unchanged from the root and the root always carries hints):

1. NUMERICS: at every node, set_face_numerics_info then
   set_node_numerics_info (build_certificates.hl:178/204, hard_lp.ml:223/257)
   tighten edge bounds (e_200_225/e_225_252), flag big triangles (bt) and set
   node bound lists (200_218/218_236/236_252/218_252).  Each nonempty
   modification is recorded as a unary Lp_split: "add_big" (split_face = the
   long-edge dart), then one "high" (split_face = node_236_252) or "mid"
   (split_face = node_218_236 @ highish) — outermost first (itlist fold).
2. HINTED SPLITS at tri nodes (split3_hard, build_certificates.hl:272): the
   branch face/dart comes from the LP-solution hint, NOT std_tri_prebranch;
   recorded as "tri" (split_face = the triangle), "edge" (split_face = dart),
   "236"/"218" (split_face = [node]).  Children:
     tri:  switch_std3  [bt c; st c]      (c = recorded split_face)
     edge: switch_edge  [e_225_252 d; e_200_225 d]
     236:  switch_node  [218_236 i; 236_252 i]   (i in highish)
     218:  switch_node  [218_252 i; 200_218 i]
   quad/pent/hex splits use the same switch4/5/6 as easy.

Replay self-checks: unary chain must match the computed numerics info list
exactly (type + split_face); quad/pent/hex split_face must equal the replayed
branch face; tri split_face must be a std triangle; 236/218 must agree with
highish membership; child counts must match.

Modes:
  make_tasks_hard.py --stats                 # walk all hard trees, checks only
  make_tasks_hard.py                         # write batch_hard_tasks.json
  make_tasks_hard.py --values-hard1 --mode full|nonumerics --workers N
      # per-terminal glpsol lnsum values for hard_1 under both replays
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO_LP = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_LP))
sys.path.insert(0, str(REPO_LP / "run"))
sys.setrecursionlimit(2_000_000)

import parse_lpcert as P  # noqa: E402
import gen_data  # noqa: E402
import gen_one  # noqa: E402
import make_tasks2a as M  # noqa: E402

BIN = Path(os.environ.get(
    "LPBIN", "/dev/shm/kepler-ref/flyspeck/formal_lp/glpk/binary"))
OUT = Path(os.environ.get("LPRUN_ROOT", "/dev/shm/lprun")) / "batch_hard_tasks.json"


# ------------------------------------------------------- generic bb helpers


def subtract(a, b):
    """OCaml List.subtract: elements of a not in b, order kept."""
    return [x for x in a if x not in b]


def card_node(bb):
    return 1 + max(v for f in gen_data.faces(bb) for v in f)


def node_list(bb):
    return list(range(card_node(bb)))


def highish(bb):
    """hard_lp.ml:151."""
    return subtract(bb["node_218_252"],
                    bb["node_218_236"] + bb["node_236_252"])


def opposite_edge(dart, bb):
    """hard_lp.ml:247 — [i;j;k] -> [j;i;k'] via first matching rotation."""
    i, j, _k = dart
    for f in gen_data.rotation(gen_data.faces(bb)):
        if f[0] == j and f[1] == i:
            return [j, i, f[2]]
    raise ValueError(f"opposite_edge: {dart} not found ({bb['hypermap_id']})")


def face_of_dart(fc, bb):
    """hard_lp.ml:153 — first face (in faces order) whose triples contain fc;
    returns its leading triple (the face itself when triangular)."""
    for f in gen_data.faces(bb):
        if fc in gen_data.triples(f):
            return f[:3]
    raise ValueError(f"face_of_dart: {fc} not found ({bb['hypermap_id']})")


# ------------------------------------------------- hard numerics (per node)


def set_face_numerics_info(bb):
    """build_certificates.hl:178 / hard_lp.ml:257.  Returns (bb', infos)."""
    def opp(xs):
        return gen_data.nub(xs + [opposite_edge(x, bb) for x in xs])
    edge_of_small = opp(gen_data.rotation(bb["std3_small"]))
    short_edge = opp(bb["d_edge_200_225"])
    long_edge = opp(bb["d_edge_225_252"])
    assert not [x for x in edge_of_small if x in long_edge], \
        "set_face_numerics: edge_of_small intersect long_edge"
    shortadds = subtract(edge_of_small + short_edge, bb["d_edge_200_225"])
    longadds = subtract(long_edge, bb["d_edge_225_252"])
    faces_of_long = gen_data.nub([face_of_dart(x, bb) for x in long_edge])
    r = [t for t in faces_of_long
         if t in gen_data.std_faces(bb) and len(t) == 3]
    assert not [x for x in gen_data.rotation(bb["std3_small"]) if x in r], \
        "set_face_numerics: rotation std3_small intersect r"
    new_big_faces = subtract(r, bb["std3_big"])
    fields = ([("e_200_225", t) for t in shortadds]
              + [("e_225_252", t) for t in longadds]
              + [("bt", t) for t in new_big_faces])
    if not fields:
        return bb, []
    new_bb = M.modify_bb(bb, False, fields)
    # NOTE: zip over the UN-nubbed long_edge (map face_of_dart long_edge),
    # elementwise — nubbing faces first would misalign the pairs.
    long_edge_faces = [(face_of_dart(x, bb), x) for x in long_edge]
    infos = []
    for f in new_big_faces:
        # assoc: first long-edge dart whose face is f
        d = next(d for fc, d in long_edge_faces if fc == f)
        infos.append(("add_big", d))
    return new_bb, infos


def set_node_numerics_info(bb):
    """build_certificates.hl:204 / hard_lp.ml:223.  Returns (bb', infos)."""
    if card_node(bb) != 13:
        return bb, []
    n_high = len(bb["node_236_252"])
    n_mid = len(bb["node_218_236"])
    hi = highish(bb)
    if n_high == 0 and n_mid + len(hi) < 2:
        return bb, []
    assert n_mid * 18 + len(hi) * 18 + n_high * 36 <= 52, \
        "set_node_numerics: bound exceeded"
    node_new_low = subtract(node_list(bb), gen_data.nub(
        bb["node_200_218"] + bb["node_218_236"]
        + bb["node_236_252"] + bb["node_218_252"]))
    vfields = ([("200_218", t) for t in node_new_low]
               + [("218_236", t) for t in hi])
    if not vfields:
        return bb, []
    new_bb = M.modify_bb(bb, False, [], vfields)
    if n_high > 0:
        infos = [("high", list(bb["node_236_252"]))]
    else:
        infos = [("mid", bb["node_218_236"] + hi)]
    return new_bb, infos


# ------------------------------------------------------------- tree replay


def switch_node(bb, i):
    """hard_lp.ml:303 — [high branch; low branch]."""
    if i in highish(bb):
        return [M.modify_bb(bb, False, [], [("218_236", i)]),
                M.modify_bb(bb, False, [], [("236_252", i)])]
    settable = subtract(node_list(bb),
                        bb["node_200_218"] + bb["node_218_236"]
                        + bb["node_236_252"])
    if i not in settable:
        raise ValueError(f"switch_node: {i} not settable "
                         f"({bb['hypermap_id']})")
    return [M.modify_bb(bb, False, [], [("218_252", i)]),
            M.modify_bb(bb, False, [], [("200_218", i)])]


def walk_hard(case, bb, numerics="full", path=()):
    """DFS over a HARD certificate tree.  Yields (bb_at_terminal, infeasible,
    path).  numerics selects which per-node numerics to apply:
    "full" (both), "noface" (node only), "nonode" (face only), "none"
    (neither — reproduces the lost easy-style replay).  Certificate unary
    numerics nodes are always consumed (and checked in "full" mode)."""
    gid = bb["hypermap_id"]
    if numerics == "full":
        bb1, info1 = set_face_numerics_info(bb)
        bb2, info2 = set_node_numerics_info(bb1)
        infos = info1 + info2
    elif numerics == "noface":
        bb2, info2 = set_node_numerics_info(bb)
        infos = None
    elif numerics == "nonode":
        bb2, info1 = set_face_numerics_info(bb)
        infos = None
    else:
        bb2 = bb
        infos = None
    # consume the unary numerics split chain (outermost first)
    while case[1] == 1 and len(P.to_list(case[2][1])) == 1:
        sc = case[2][0][2]
        stype, sface = sc[0], P.to_list(sc[1])
        if stype not in ("add_big", "high", "mid"):
            raise ValueError(f"unary split of unexpected type {stype} "
                             f"({gid} at {path})")
        if infos is not None:
            if not infos:
                raise ValueError(f"certificate has unary {stype} split but "
                                 f"replay computed no numerics change "
                                 f"({gid} at {path})")
            etype, eface = infos.pop(0)
            if stype != etype or sface != eface:
                raise ValueError(
                    f"numerics mismatch: certificate ({stype}, {sface}) vs "
                    f"replay ({etype}, {eface}) ({gid} at {path})")
        case = P.to_list(case[2][1])[0]
        path = path + ((stype,),)
    if infos is not None and infos:
        raise ValueError(f"replay computed numerics {infos} but certificate "
                         f"has no unary splits ({gid} at {path})")
    if case[1] == 0:  # Lp_terminal
        t = case[2][0][2]
        yield bb2, bool(t[1]), path
        return
    sc = case[2][0][2]
    stype, sface = sc[0], P.to_list(sc[1])
    children = P.to_list(case[2][1])
    if stype == "tri":
        # split3_hard: face comes from the hint; recorded as split_face
        c = sface
        std_tris = gen_data.rotation(
            [f for f in bb2["std_faces_not_super"] if len(f) == 3])
        if c not in std_tris:
            raise ValueError(f"tri split_face {c} not a std triangle "
                             f"({gid} at {path})")
        bbs = [M.modify_bb(bb2, False, [("bt", c)]),
               M.modify_bb(bb2, False, [("st", c)])]
    elif stype == "edge":
        d = sface
        bbs = [M.modify_bb(bb2, False, [("e_225_252", d)]),
               M.modify_bb(bb2, False, [("e_200_225", d)])]
    elif stype in ("236", "218"):
        i = sface[0]
        if numerics == "full":
            if (stype == "236") != (i in highish(bb2)):
                raise ValueError(f"node split {stype} {i} disagrees with "
                                 f"highish ({gid} at {path})")
            bbs = switch_node(bb2, i)
        else:
            # degraded replay: branch by recorded type only (bb state
            # without full numerics may not agree with highish)
            if stype == "236":
                bbs = [M.modify_bb(bb2, False, [], [("218_236", i)]),
                       M.modify_bb(bb2, False, [], [("236_252", i)])]
            else:
                bbs = [M.modify_bb(bb2, False, [], [("218_252", i)]),
                       M.modify_bb(bb2, False, [], [("200_218", i)])]
    elif stype in ("quad", "pent", "hex"):
        fc, bbs = M.SWITCH[stype](bb2)
        if sface != fc:
            raise ValueError(f"split_face mismatch: certificate {sface} vs "
                             f"replay {fc} ({gid} at {path})")
    else:
        raise ValueError(f"unknown split type {stype} ({gid} at {path})")
    if len(children) != len(bbs):
        raise ValueError(f"child count mismatch: certificate "
                         f"{len(children)} vs switch {len(bbs)} "
                         f"({stype}, {gid} at {path})")
    for k, (ch, bb3) in enumerate(zip(children, bbs)):
        yield from walk_hard(ch, bb3, numerics, path + ((stype, k),))


def hard_files():
    """hard_*.dat in numeric order; hard_7 is shipped as .tar.gz."""
    out = []
    for n in range(1, 1000):
        p = BIN / f"hard_{n}.dat"
        if p.exists():
            out.append((n, p))
            continue
        tgz = BIN / f"hard_{n}.tar.gz"
        if tgz.exists():
            import tarfile
            with tarfile.open(tgz) as tf:
                data = tf.extractfile(f"hard_{n}.dat").read()
            tmp = Path(tempfile.gettempdir()) / f"hard_{n}.dat"
            tmp.write_bytes(data)
            out.append((n, tmp))
            continue
        break
    return out


def build_tasks(numerics="full", only_key=None):
    """Returns list of task dicts (without data_text when only_key is None...
    no — always with data_text).  only_key restricts to one file number."""
    tasks = []
    for n, path in hard_files():
        if only_key is not None and n != only_key:
            continue
        certs = [P.to_cert(v) for v in P.to_list(P.read_marshal(str(path)))]
        for gi, c in enumerate(certs):
            root = gen_data.root_bb(c["hypermap_string"])
            graph = root["hypermap_id"]
            for ti, (bb, infeasible, _path) in enumerate(
                    walk_hard(c["root_case"], root, numerics)):
                tasks.append({
                    "id": f"{graph}_t{ti:04d}",
                    "graph": graph,
                    "ti": ti,
                    "key": f"hard_{n}",
                    "gi": gi,
                    "infeasible": infeasible,
                    "data_text": gen_data.ampl_of_bb(bb),
                })
    return tasks


# ------------------------------------------- hard_1 deviation experiment


_MODEL_CACHE = []


def lnsum_value(data_text, workdir):
    """Solve the terminal LP with glpsol; returns optimal lnsum value,
    or None when primal-infeasible."""
    if not _MODEL_CACHE:
        _MODEL_CACHE.append(gen_one.build_model2())
    (workdir / "model2.mod").write_text(_MODEL_CACHE[0])
    (workdir / "data.txt").write_text(data_text)
    r = subprocess.run(
        [gen_one.GLPSOL, "-m", "model2.mod", "-d", "data.txt",
         "-o", str(workdir / "sol.txt")],
        cwd=workdir, capture_output=True, text=True, timeout=600)
    sol = (workdir / "sol.txt").read_text() if (workdir / "sol.txt").exists() \
        else ""
    for line in sol.splitlines():
        if line.startswith("Objective:"):
            return float(line.split("=")[1].split()[0])
    if "NO PRIMAL FEASIBLE" in r.stdout + r.stderr + sol:
        return None
    raise RuntimeError(f"glpsol value parse failed: "
                       f"{r.stdout[-500:]} {r.stderr[-500:]} {sol[:200]}")


def values_hard1(mode, workers, out_path):
    tasks = build_tasks(numerics=mode, only_key=1)
    print(f"[values] hard_1: {len(tasks)} terminals, mode={mode}", flush=True)
    root = Path(os.environ.get("LPRUN_ROOT", "/dev/shm/lprun"))

    def one(t):
        wdir = root / "work_values" / f"{mode}_{t['id']}"
        wdir.mkdir(parents=True, exist_ok=True)
        try:
            v = None if t["infeasible"] else lnsum_value(t["data_text"], wdir)
            return {"id": t["id"], "ti": t["ti"],
                    "infeasible": t["infeasible"], "value": v}
        finally:
            import shutil
            shutil.rmtree(wdir, ignore_errors=True)

    results = []
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for i, r in enumerate(ex.map(one, tasks)):
            results.append(r)
            if (i + 1) % 100 == 0:
                print(f"[values] {i + 1}/{len(tasks)}", flush=True)
                Path(out_path).write_text(json.dumps(results))
    Path(out_path).write_text(json.dumps(results))
    print(f"[values] wrote {out_path} ({len(results)} rows)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stats", action="store_true")
    ap.add_argument("--values-hard1", action="store_true")
    ap.add_argument("--mode", choices=["full", "none", "noface", "nonode"],
                    default="full")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()

    if a.values_hard1:
        out = a.out or f"/dev/shm/lprun/hard1_values_{a.mode}.json"
        values_hard1(a.mode, a.workers, out)
        return 0

    tasks = build_tasks()
    n_inf = sum(1 for t in tasks if t["infeasible"])
    graphs = {t["graph"] for t in tasks}
    ids = [t["id"] for t in tasks]
    assert len(set(ids)) == len(ids), "duplicate task ids"
    print(f"[make_tasks_hard] {len(graphs)} hard graphs, {len(tasks)} "
          f"terminal tasks, {n_inf} infeasible")
    if not a.stats:
        OUT.write_text(json.dumps(tasks))
        print(f"[make_tasks_hard] wrote {OUT} ({OUT.stat().st_size} bytes)")
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
