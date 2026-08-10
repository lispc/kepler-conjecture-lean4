#!/usr/bin/env python3
"""Emit a few Tri-tree nodes as Lean literals to time kernel `decide` replay.

Usage: python3 kern_probe.py > /tmp/kern_probe.lean
"""
import sys
import pathlib

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import enumerate as E


def face_lean(f):
    vs = ", ".join(map(str, f[0]))
    return f"⟨[{vs}], {'true' if f[1] else 'false'}⟩"


def graph_lean(g):
    fs = ", ".join(face_lean(f) for f in E.faces(g))
    fla = ", ".join("[" + ", ".join(face_lean(f) for f in fl) + "]"
                     for fl in E.faceListAt(g))
    hs = ", ".join(map(str, E.heights(g)))
    return (f"⟨[{fs}], {E.countVertices(g)}, [{fla}], [{hs}]⟩")


def main():
    # BFS the Tri tree, collect one non-final node per depth
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    maxdepth = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    # follow a first-child path down the tree (cheap for big seeds)
    picked = []
    g = E.Seed(p)
    for depth in range(maxdepth + 1):
        if E.finalGraph(g):
            break
        picked.append((depth, g))
        cs = E.next_tame(p, g)
        if not cs:
            break
        g = cs[0]

    print("import Kepler.Graphs")
    print("namespace Kepler.Graphs")
    print("set_option maxHeartbeats 0")
    for d, g in picked:
        cs = E.next_tame0(p, g)  # unfiltered children (next_tame adds filter)
        cs2 = E.next_tame(p, g)
        print(f"-- depth {d}: faces={len(E.faces(g))} "
              f"children0={len(cs)} children_tame={len(cs2)}")
        print(f"set_option maxRecDepth 100000 in")
        print(f"example : next_tame {p} {graph_lean(g)} =")
        print(f"    [{', '.join(graph_lean(c) for c in cs2)}] := by decide")
    print("end Kepler.Graphs")


if __name__ == "__main__":
    main()
