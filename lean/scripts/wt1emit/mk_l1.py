#!/usr/bin/env python3
"""Derive the L1 emission from gen_m9's output for one box (see docstring v2)."""
import re
import sys

DROP = re.compile(r'^theorem (ev_|p[0-9]_|op_)')
ROOT_NAMES = {'ev_Top', 'p0_Top', 'p1_Top', 'p2_Top'}
RW_EV = re.compile(r'^\s*rw \[ev_[A-Za-z0-9]+\]\s*$')


def main(src, dst):
    lines = open(src).read().splitlines()
    out = []
    sec = None
    roots = {}
    i = 0
    while i < len(lines):
        ln = lines[i]
        m = re.match(r'^namespace (Box|Pt)$', ln)
        if m:
            sec = m.group(1)
        if re.match(r'^end (Box|Pt)$', ln):
            sec = None
        m = DROP.match(ln)
        if m and sec:
            for nm in ROOT_NAMES:
                if re.match(r'^theorem %s : ' % nm, ln):
                    roots[(sec, nm)] = ln.split(' : ', 1)[1].split(' :=', 1)[0].strip()
            j = i + 1
            while j < len(lines) and lines[j].strip() != '':
                j += 1
            i = j + 1
            continue
        if RW_EV.match(ln):
            i += 1
            continue
        ln2 = re.sub(r'from ev_[A-Za-z0-9]+\]', 'from rfl]', ln)
        ln2 = re.sub(r'\(by rw \[ev_[A-Za-z0-9]+\]; decide\)', '(by decide)', ln2)
        out.append(ln2)
        i += 1
    text = []
    for ln in out:
        if ln == 'end Box' and ('Box', 'p0_Top') in roots:
            for k in ('p0_Top', 'p1_Top', 'p2_Top'):
                text.append('theorem %s : %s := by rfl' % (k, roots[('Box', k)]))
                text.append('')
            text.append(ln)
        elif ln == 'end Pt' and ('Pt', 'ev_Top') in roots:
            text.append('theorem ev_Top : %s := by rfl' % roots[('Pt', 'ev_Top')])
            text.append('')
            text.append(ln)
        else:
            text.append(ln)
    open(dst, 'w').write('\n'.join(text) + '\n')
    print('wrote %s: %d lines (src %d)' % (dst, len(text), len(lines)))
    print('roots: %s' % sorted(roots))


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
