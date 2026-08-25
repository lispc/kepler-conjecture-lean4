#!/usr/bin/env python3
"""parse_lpcert.py — pure-Python reader for Flyspeck OCaml-Marshal lp_certificate files.

Reads `reference/flyspeck/formal_lp/glpk/binary/easy_*.dat` (OCaml Marshal
small format, magic 84 95 a6 be), decodes the `lp_certificate list` structure
defined in `formal_lp/hypermap/main/lp_certificate.hl:1-35`, and reports
per-graph terminal counts.  With `--extract N`, prints the hypermap string of
the N-th certificate (index into the list) for data-section regeneration.

OCaml type being decoded:

    type constraint_type = string * int list * int64 list
    type terminal_case = { precision:int; infeasible:bool;
        constraints: constraint_type list; target_variables: constraint_type list;
        variable_bounds: constraint_type list }
    type split_case = { split_type:string; split_face:int list }
    type lp_certificate_case = Lp_terminal of terminal_case
                             | Lp_split of split_case * lp_certificate_case list
    type lp_certificate = { hypermap_string:string; root_case:lp_certificate_case }

Marshal format notes (OCaml byterun/extern.c, intern.c):
  small int    0x40..0x7F  value = code & 0x3F
  small string 0x20..0x3F  length = code & 0x1F
  small block  0x80..0xFF  size = (code>>4)&7, tag = code&0xF
  0x00/01/02/03 INT8/16/32/64 (big-endian, signed)
  0x04/05/06    SHARED8/16/32 (offset back into object table)
  0x08          BLOCK32 (header u32: size = h>>10, tag = h&0xFF)
  0x09/0A       STRING8/32 (length u8/u32)
  0x12          CUSTOM: NUL-terminated ident, then payload ("_j" = int64, 8 bytes BE)
  OCaml int is sign-extended from the code width (63-bit); blocks are
  registered in the object table *before* their fields are read.

Usage:
  parse_lpcert.py FILE.dat                # stats for every certificate
  parse_lpcert.py FILE.dat --extract N    # print hypermap_string of cert N
"""

import argparse
import struct
import sys


class Reader:
    def __init__(self, data: bytes):
        self.data = data
        self.pos = 0
        self.objects: list = []  # sharing table

    def u8(self) -> int:
        b = self.data[self.pos]
        self.pos += 1
        return b

    def read(self, n: int) -> bytes:
        b = self.data[self.pos : self.pos + n]
        if len(b) != n:
            raise ValueError("unexpected EOF")
        self.pos += n
        return b

    def uint(self, n: int) -> int:
        return int.from_bytes(self.read(n), "big")

    def sint(self, n: int) -> int:
        return int.from_bytes(self.read(n), "big", signed=True)

    def value(self):
        code = self.u8()
        if code >= 0x40:
            if code >= 0x80:  # small block
                size, tag = (code >> 4) & 0x7, code & 0xF
                return self.block(tag, size)
            return code & 0x3F  # small int
        if code >= 0x20:  # small string
            return self.string(code & 0x1F)
        if code == 0x00:
            return self.sint(1)
        if code == 0x01:
            return self.sint(2)
        if code == 0x02:
            return self.sint(4)
        if code == 0x03:
            return self.sint(8)
        if code in (0x04, 0x05, 0x06):  # shared
            n = {0x04: 1, 0x05: 2, 0x06: 4}[code]
            offset = self.uint(n)
            idx = len(self.objects) - offset
            if not (0 <= idx < len(self.objects)):
                raise ValueError(f"bad sharing offset {offset}")
            return self.objects[idx]
        if code == 0x08:  # BLOCK32
            header = self.uint(4)
            return self.block(header & 0xFF, header >> 10)
        if code == 0x09:
            return self.string(self.u8())
        if code == 0x0A:
            return self.string(self.uint(4))
        if code == 0x12:  # CUSTOM
            end = self.data.index(b"\x00", self.pos)
            ident = self.data[self.pos : end].decode("ascii")
            self.pos = end + 1
            if ident != "_j":
                raise ValueError(f"unsupported custom block {ident!r}")
            v = self.sint(8)
            self.objects.append(v)
            return v
        raise ValueError(f"unsupported marshal code 0x{code:02x} at {self.pos - 1:#x}")

    def block(self, tag: int, size: int):
        b = ("block", tag, [None] * size)
        self.objects.append(b)  # registered before fields (OCaml semantics)
        b[2][:] = [self.value() for _ in range(size)]
        return b

    def string(self, n: int):
        s = self.read(n).decode("ascii")
        self.objects.append(s)
        return s


def read_marshal(path):
    data = open(path, "rb").read()
    magic, dlen, nobj, s32, s64 = struct.unpack(">5I", data[:20])
    if magic != 0x8495A6BE:
        raise ValueError(f"bad magic {magic:#x} (want small-format 0x8495a6be)")
    r = Reader(data[20 : 20 + dlen])
    v = r.value()
    if r.pos != len(r.data):
        raise ValueError(f"trailing bytes: used {r.pos} of {len(r.data)}")
    if len(r.objects) != nobj:
        raise ValueError(f"object count mismatch: {len(r.objects)} vs header {nobj}")
    return v


# ---------------------------------------------------------------- structure


def to_list(v):
    """OCaml 'a list -> python list ([] = int 0, cons = block tag 0 size 2)."""
    out = []
    while v != 0:
        tag, (h, t) = v[1], v[2]
        assert tag == 0, f"bad list node tag {tag}"
        out.append(h)
        v = t
    return out


def to_cert(v):
    """block tag 0 size 2: (hypermap_string, root_case)."""
    assert v[0] == "block" and v[1] == 0 and len(v[2]) == 2
    return {"hypermap_string": v[2][0], "root_case": v[2][1]}


def count_terminals(case) -> int:
    tag = case[1]
    if tag == 0:  # Lp_terminal
        return 1
    assert tag == 1, f"bad case tag {tag}"
    return sum(count_terminals(c) for c in to_list(case[2][1]))


def terminal_info(case):
    """(n_terminals, n_infeasible) for the whole tree."""
    if case[1] == 0:
        t = case[2][0]
        assert t[0] == "block" and len(t[2]) == 5
        return 1, (1 if t[2][1] else 0)
    nt = ni = 0
    for c in to_list(case[2][1]):
        a, b = terminal_info(c)
        nt += a
        ni += b
    return nt, ni


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("dat")
    ap.add_argument("--extract", type=int, default=None,
                    help="print hypermap_string of the N-th certificate")
    ap.add_argument("--tree", type=int, default=None,
                    help="print split-tree summary of the N-th certificate")
    args = ap.parse_args()

    certs = [to_cert(v) for v in to_list(read_marshal(args.dat))]
    if args.extract is not None:
        print(certs[args.extract]["hypermap_string"])
        return 0
    if args.tree is not None:
        def show(case, depth=0):
            pad = "  " * depth
            if case[1] == 0:
                t = case[2][0][2]
                print(f"{pad}terminal precision={t[0]} infeasible={bool(t[1])} "
                      f"nconstr={len(to_list(t[2]))}")
            else:
                sc = case[2][0][2]
                print(f"{pad}split {sc[0]} face={to_list(sc[1])}")
                for c in to_list(case[2][1]):
                    show(c, depth + 1)
        show(certs[args.tree]["root_case"])
        return 0

    print(f"{len(certs)} certificates in {args.dat}")
    hist: dict[int, int] = {}
    min_terms = min(count_terminals(c["root_case"]) for c in certs)
    single_ok = []
    for i, c in enumerate(certs):
        nt, ni = terminal_info(c["root_case"])
        hist[nt] = hist.get(nt, 0) + 1
        if nt == min_terms and ni == 0:
            single_ok.append((i, c["hypermap_string"].split()[0]))
    print("terminal-count histogram (terminals: #graphs):")
    for k in sorted(hist):
        print(f"  {k:5d}: {hist[k]}")
    print(f"min terminals = {min_terms}; "
          f"{len(single_ok)} graphs with {min_terms} terminal(s), none infeasible; first 10:")
    for i, hid in single_ok[:10]:
        print(f"  index {i}: hypermap_id {hid}")
    return 0


if __name__ == "__main__":
    # Marshal cons-lists nest deeply; run with a large stack.
    import threading

    sys.setrecursionlimit(2_000_000)
    threading.stack_size(1024 * 1024 * 1024)
    result = []

    def run():
        result.append(main())

    t = threading.Thread(target=run)
    t.start()
    t.join()
    sys.exit(result[0])
