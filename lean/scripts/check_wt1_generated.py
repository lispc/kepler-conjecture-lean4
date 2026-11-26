#!/usr/bin/env python3
"""check_wt1_generated.py — guard: are the 221 generated wt1 modules present and current?

Hash-only (no generation, no Lean): compares
`lean/Kepler/Text/TaylorSecond/W1DC_*.lean` against
`lean/scripts/wt1emit/manifest.sha256`.  Exit 0 = all 221 byte-identical,
1 = something missing or stale (the repair command is printed).

Used by `make check-wt1`; see `lean/scripts/wt1emit/README.md`.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EMIT = os.path.join(HERE, 'wt1emit')
sys.path.insert(0, EMIT)

import gen_all  # noqa: E402


def main():
    rows, _by_name = gen_all.load_manifest()
    rc = gen_all.cmd_verify(rows, gen_all.DEFAULT_OUT)
    print('check_wt1_generated: %s (%d files, dir=%s)'
          % ('OK' if rc == 0 else 'FAIL', len(rows), gen_all.DEFAULT_OUT))
    if rc != 0:
        print('repair: make gen-wt1   (or: python3 -I lean/scripts/wt1emit/gen_all.py)')
    return rc


if __name__ == '__main__':
    sys.exit(main())
