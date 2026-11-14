"""Parse the emitted Lean hull-expression text into a Python AST."""
import re, sys, json
from fractions import Fraction as F

TOK = re.compile(r"\(|\)|[^\s()]+")

def tokenize(s):
    return TOK.findall(s)

class P:
    def __init__(self, toks):
        self.t = toks; self.i = 0
    def peek(self): return self.t[self.i]
    def next(self): self.i += 1; return self.t[self.i-1]
    def parse(self):
        # node := '(' OP args ')'   where atom := '(.const ⟨m, e⟩)' | '(.var k)'
        tok = self.next()
        assert tok == '(', tok
        op = self.next()
        if not op.startswith('.'):
            # parenthesised atom, e.g. (-64)
            parts = [op]
            while self.peek() != ')':
                parts.append(self.next())
            self.next()
            return '(' + ' '.join(parts) + ')'
        args = []
        while self.peek() != ')':
            if self.peek() == '(':
                args.append(self.parse())
            else:
                args.append(self.next())
        self.next()  # ')'
        return (op, args)

def parse_const(tok):
    # '⟨m,' 'e⟩'  or '⟨m,e⟩'
    t = tok.replace('⟨','').replace('⟩','').replace(',',' ')
    m, e = t.split()
    return (int(m), int(e))

def load_expr(path, name='TskXLLIPLSExpr'):
    txt = open(path).read()
    if name is None:
        import re as _re
        m = _re.search(r'def (\w+Expr) ', txt)
        name = m.group(1)
    i = txt.index('def ' + name)
    j = txt.index(':=', i) + 2
    # expression ends at the line that starts with a non-space and is not continuation
    rest = txt[j:]
    depth = 0; end = None
    for k, ch in enumerate(rest):
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                end = k+1
                break
    s = rest[:end].strip()
    toks = tokenize(s)
    p = P(toks)
    ast = p.parse()
    assert p.i == len(toks), (p.i, len(toks))
    return ast

def infer_sort_print(ast):
    """Print the tree with '.const' args re-parsed (const carries 2 tokens)."""
    op, args = ast
    if op == '.const':
        return f"(.const {parse_const(' '.join(args))})"
    out = []
    for a in args:
        if isinstance(a, tuple):
            out.append(print_node(a))
        else:
            out.append(a)
    return f"({op} {' '.join(out)})"

def print_node(ast):
    op, args = ast
    if op == '.const':
        m, e = parse_const(' '.join(args))
        return f"(.const {m}:{e})"
    out = []
    for a in args:
        out.append(print_node(a) if isinstance(a, tuple) else a)
    return f"({op} {' '.join(out)})"

def count_nodes(ast):
    op, args = ast
    n = 1
    c = {op: 1}
    for a in args:
        if isinstance(a, tuple):
            k, cc = count_nodes(a)
            n += k
            for kk, v in cc.items(): c[kk] = c.get(kk, 0) + v
    return n, c

if __name__ == '__main__':
    ast = load_expr(sys.argv[1])
    n, c = count_nodes(ast)
    print('nodes', n)
    print(c)
    print(print_node(ast)[:1500])
