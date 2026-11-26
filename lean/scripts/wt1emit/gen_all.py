#!/usr/bin/env python3
"""gen_all.py — deterministic rebuild of the 221 generated wt1 modules.

Chain per box (both generators are *untrusted*, the Lean kernel re-checks
every emitted literal):

    gen_m9.py --id <stem> --out <tmp>/raw.lean
    mk_l1.py  <tmp>/raw.lean <tmp>/<stem>.lean

`manifest.sha256` records the sha256 of the 221 files as landed (computed from
the git blobs of commit 7855a963, not from this generator).  Every emitted
file is compared against that record; a mismatch aborts instead of silently
installing a drifted file.

Usage:
    python3 -I lean/scripts/wt1emit/gen_all.py                 # create/repair (idempotent)
    python3 -I lean/scripts/wt1emit/gen_all.py --check         # generate in tmp, write nothing
    python3 -I lean/scripts/wt1emit/gen_all.py --verify-manifest   # hash-only guard
    python3 -I lean/scripts/wt1emit/gen_all.py --only <stem> --out-dir /tmp/x
    python3 -I lean/scripts/wt1emit/gen_all.py --force         # rewrite even if up to date

Exit codes: 0 ok, 1 verification/drift failure, 2 usage error.
"""
import argparse
import hashlib
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

GEN_M9 = os.path.join(HERE, 'gen_m9.py')
MK_L1 = os.path.join(HERE, 'mk_l1.py')
BOXES = os.path.join(HERE, 'boxes221.json')
MANIFEST = os.path.join(HERE, 'manifest.sha256')

LEAN_DIR = os.path.dirname(os.path.dirname(HERE))          # <repo>/lean
REPO_DIR = os.path.dirname(LEAN_DIR)                       # <repo>
DEFAULT_OUT = os.path.join(LEAN_DIR, 'Kepler', 'Text', 'TaylorSecond')


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load_manifest(path=MANIFEST):
    """[(sha, repo-relative path)] in file order; names must be unique."""
    rows = []
    seen = {}
    with open(path, encoding='utf-8') as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split(None, 1)
            if len(parts) != 2:
                raise SystemExit('%s:%d: bad manifest line' % (path, lineno))
            digest, rel = parts[0], parts[1].strip()
            base = os.path.basename(rel)
            stem = base[:-len('.lean')] if base.endswith('.lean') else base
            if stem in seen:
                raise SystemExit('%s:%d: duplicate file name %s' % (path, lineno, base))
            seen[stem] = digest
            rows.append((digest, rel))
    return rows, seen


def box_ids(path=BOXES):
    import json
    with open(path, encoding='utf-8') as fh:
        boxes = json.load(fh)
    ids = [r['id'] for r in boxes]
    if len(set(ids)) != len(ids):
        raise SystemExit('%s: box ids are not unique' % path)
    return ids


def _run(cmd):
    env = dict(os.environ)
    env['PYTHONUTF8'] = '1'
    # keep the checkout clean: no __pycache__ next to the generators
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          env=env, universal_newlines=True)
    if proc.returncode != 0:
        raise SystemExit('command failed (rc=%d): %s\n%s'
                         % (proc.returncode, ' '.join(cmd), proc.stdout))
    return proc.stdout


def emit_one(stem, tmpdir):
    """Run the generator chain for one box; return the path of the emitted file."""
    raw = os.path.join(tmpdir, stem + '.raw.lean')
    out = os.path.join(tmpdir, stem + '.lean')
    _run([sys.executable, '-I', GEN_M9, '--boxes', BOXES, '--id', stem, '--out', raw])
    _run([sys.executable, '-I', MK_L1, raw, out])
    return out


def _target(out_dir, stem):
    return os.path.join(out_dir, stem + '.lean')


def cmd_verify(rows, out_dir):
    """Hash-only check of the 221 generated files (never generates)."""
    bad = []
    for digest, rel in rows:
        base = os.path.basename(rel)
        stem = base[:-len('.lean')] if base.endswith('.lean') else base
        path = _target(out_dir, stem)
        if not os.path.exists(path):
            alt = os.path.join(REPO_DIR, rel)
            path = alt if os.path.exists(alt) else None
        if path is None:
            bad.append((base, 'MISSING', digest))
        else:
            got = sha256_file(path)
            if got != digest:
                bad.append((base, 'SHA-MISMATCH', got))
    for base, why, got in bad:
        print('%-14s %s  got=%s' % (why, base, got))
    print('verify-manifest: %d files, %d bad' % (len(rows), len(bad)))
    if bad:
        print('repair: python3 -I lean/scripts/wt1emit/gen_all.py --force')
        return 1
    return 0


def cmd_generate(ids, by_name, out_dir, only, check, force, quiet):
    wanted = [s for s in ids if not only or s in only]
    if only:
        unknown = sorted(set(only) - set(ids))
        if unknown:
            raise SystemExit('--only: unknown box id(s): %s' % ', '.join(unknown))
    os.makedirs(out_dir, exist_ok=True) if not check else None
    stats = dict(up_to_date=0, written=0, would_write=0, mismatch=0)
    tmpdir = tempfile.mkdtemp(prefix='wt1emit-')
    try:
        for i, stem in enumerate(wanted, 1):
            if stem not in by_name:
                raise SystemExit('%s: not in manifest.sha256' % stem)
            expected = by_name[stem]
            target = _target(out_dir, stem)
            if not check and not force and os.path.exists(target) \
                    and sha256_file(target) == expected:
                stats['up_to_date'] += 1
                continue
            produced = emit_one(stem, tmpdir)
            got = sha256_file(produced)
            if got != expected:
                stats['mismatch'] += 1
                print('DRIFT %s  expected=%s got=%s' % (stem, expected, got))
                continue
            if check:
                same = os.path.exists(target) and sha256_file(target) == expected
                stats['up_to_date' if same else 'would_write'] += 1
                if not same:
                    print('WOULD-WRITE %s' % stem)
                continue
            if os.path.exists(target) and sha256_file(target) == expected:
                stats['up_to_date'] += 1
                continue
            tmp_target = target + '.wt1tmp'
            with open(produced, 'rb') as src, open(tmp_target, 'wb') as dst:
                dst.write(src.read())
            os.replace(tmp_target, target)
            stats['written'] += 1
            if not quiet:
                print('wrote %s' % target)
            if i % 25 == 0:
                print('... %d/%d' % (i, len(wanted)))
    finally:
        for name in os.listdir(tmpdir):
            os.unlink(os.path.join(tmpdir, name))
        os.rmdir(tmpdir)
    mode = 'check' if check else 'generate'
    print('%s: %d target(s) — up-to-date=%d written=%d would-write=%d mismatch=%d dir=%s'
          % (mode, len(wanted), stats['up_to_date'], stats['written'],
             stats['would_write'], stats['mismatch'], out_dir))
    return 1 if stats['mismatch'] else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--out-dir', default=DEFAULT_OUT,
                    help='target directory (default: lean/Kepler/Text/TaylorSecond)')
    ap.add_argument('--only', action='append', default=None,
                    help='regenerate/check only this box id (repeatable)')
    ap.add_argument('--check', action='store_true',
                    help='emit to a temp dir, compare, write nothing')
    ap.add_argument('--verify-manifest', action='store_true',
                    help='hash the files on disk against manifest.sha256; no generation')
    ap.add_argument('--if-missing', action='store_true',
                    help='accepted for readability; the default already skips up-to-date files')
    ap.add_argument('--force', action='store_true', help='rewrite even when up to date')
    ap.add_argument('--quiet', action='store_true')
    args = ap.parse_args(argv)

    rows, by_name = load_manifest()
    if args.verify_manifest:
        return cmd_verify(rows, args.out_dir)
    ids = box_ids()
    missing = [s for s in ids if s not in by_name]
    extra = [s for s in by_name if s not in set(ids)]
    if missing or extra:
        print('manifest/manifest-set mismatch: missing=%d extra=%d' % (len(missing), len(extra)))
        if missing:
            print('  missing:', ', '.join(missing[:5]))
        if extra:
            print('  extra:  ', ', '.join(extra[:5]))
        return 1
    return cmd_generate(ids, by_name, args.out_dir, args.only, args.check,
                        args.force, args.quiet)


if __name__ == '__main__':
    sys.exit(main())
