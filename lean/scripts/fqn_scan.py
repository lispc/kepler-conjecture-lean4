#!/usr/bin/env python3
"""Scan lean/Kepler for duplicate fully-qualified names across files.

Correctly tracks namespace/section stacks, skips `private` decls
(name-mangled by Lean, never conflict), and captures decl bodies so
duplicates can be classified: identical / renamed-twin / divergent.
"""
import os, re, sys, hashlib, json, collections

ROOT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "Kepler")

DECL_RE = re.compile(
    r'^\s*(?:@[\w\s\[\]().,*]+\s+)?'
    r'(noncomputable\s+)?(private\s+)?(protected\s+)?'
    r'(def|theorem|abbrev|opaque|lemma|instance|axiom|constant|structure|inductive|class)\s+'
    r'([!?\w\'\.]+)')
NS_RE = re.compile(r'^\s*namespace\s+([\w\.]+)')
SECTION_RE = re.compile(r'^\s*section\b')
END_RE = re.compile(r'^\s*end\b\s*([\w\.]*)')
# a line that terminates the previous decl body
STOP_RE = re.compile(
    r'^(@\[|/--|/-|noncomputable |private |protected |def |theorem |abbrev |'
    r'opaque |lemma |instance |axiom |constant |structure |inductive |class |'
    r'namespace |section |end |#|open |variable |universe )')

def strip_comments(lines):
    out_lines = []
    in_comment = False
    for line in lines:
        out = []
        j = 0
        while j < len(line):
            if in_comment:
                k = line.find("-/", j)
                if k == -1:
                    j = len(line); continue
                in_comment = False; j = k + 2
            else:
                k = line.find("/-", j)
                if k == -1:
                    out.append(line[j:]); j = len(line)
                else:
                    out.append(line[k:k] + line[j:k]); in_comment = True; j = k + 2
        out_lines.append("".join(out))
    return out_lines

defs = collections.defaultdict(list)

for dirpath, _, files in os.walk(ROOT):
    for f in sorted(files):
        if not f.endswith(".lean"):
            continue
        path = os.path.join(dirpath, f)
        rel = os.path.relpath(path, ROOT)
        with open(path, encoding="utf-8") as fh:
            raw_lines = fh.readlines()
        lines = strip_comments(raw_lines)
        stack = []  # ('ns', name) or ('section',)
        decls = []  # (line_no, kind, name, private)
        for i, line in enumerate(lines, 1):
            s = line.strip()
            if s.startswith("--"):
                continue
            m = NS_RE.match(line)
            if m:
                stack.append(("ns", m.group(1)))
                continue
            if SECTION_RE.match(line):
                stack.append(("section", None))
                continue
            m = END_RE.match(line)
            if m:
                if stack:
                    stack.pop()
                continue
            m = DECL_RE.match(line)
            if m:
                priv = bool(m.group(2))
                kind, name = m.group(4), m.group(5)
                ns = ".".join(n for t, n in stack if t == "ns")
                fqn = (ns + "." + name) if ns else name
                decls.append((i, kind, fqn, priv))
        # capture bodies: decl line -> next STOP line (col 0)
        for idx, (i, kind, fqn, priv) in enumerate(decls):
            j = i  # 0-based i = line i
            body = [lines[i - 1]]
            k = i
            while k < len(lines):
                l = lines[k]
                if l.strip() and STOP_RE.match(l):
                    break
                body.append(l)
                k += 1
            text = "".join(body).strip()
            defs[fqn].append({
                "file": rel, "line": i, "kind": kind,
                "private": priv,
                "hash": hashlib.sha1(text.encode()).hexdigest()[:12],
                "sig": text.split(":=")[0].split(":", 1)[0].strip(),
            })

dup = {k: v for k, v in defs.items()
       if len({x["file"] for x in v if not x["private"]}) > 1}
out = {}
for k in sorted(dup):
    pubs = [x for x in dup[k] if not x["private"]]
    hashes = {x["hash"] for x in pubs}
    sigs = {x["sig"] for x in pubs}
    cls = "identical" if len(hashes) == 1 else (
        "same-signature" if len(sigs) == 1 else "divergent")
    out[k] = {"class": cls, "locs": pubs}

print(json.dumps(out, indent=1, ensure_ascii=False))
print(f"\nTOTAL cross-file duplicate FQNs (non-private): {len(out)}",
      file=sys.stderr)
