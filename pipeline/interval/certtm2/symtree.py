"""symtree.py — the C1 supplier proper: symbolic second partials as
expression trees, evaluated over the leaf box with certified dyadic
intervals.

This mirrors the HOL `formal_ineqs` mass-production recipe
(`informal_taylor.hl:81-104`: the second partials are supplied in
*expression form* — `partials2` — and evaluated over the full box with
interval arithmetic; see JET3_PLAN §2.3 / §4) and the planned Lean C1a
shape (`derivIExprM` applied twice, then a hull/interval evaluation of
the resulting closed-form tree).

Why not plain second-order interval AD: the AD chain multiplies
*intermediate derivative intervals* at every node; on the wide pilot
leaves (free dims up to 0.23) that wrapping explodes (measured: a single
dihY value enclosure 0.45 wide where the true range is ~0.012 — kept as
the `--cert-mode ad` comparison in the validation data).  The tree form
evaluates each closed-form partial DIRECTLY over the box: no intermediate
derivative intervals, wrapping stays at the level of the expression's own
sub-terms (HOL parity).

Node IR (immutable tuples; DAG sharing by object identity, evaluation is
memoized per node id — linear time in the DAG):

  ('const', Fraction)            exact rational constant
  ('var', i)                     y_i
  ('neg', a) ('add',a,b) ('sub',a,b) ('mul',a,b) ('div',a,b)
  ('sq', a)                      tight square {u^2} (NOT the interval product)
  ('sqrt', a, tag)               tag None | 'delta' | 'rad:<k>':
                                 certified lower-end floors on the radicand
                                 ('delta': >= exact vertex min of deltaX over
                                   the box — deltaX is separately concave in
                                   each x_i, so its box minimum is at a vertex;
                                  'rad:<k>': >= 4 * y_k.lo * deltaMin — both
                                   factors are positive, so the product is
                                   bounded below pointwise)
  ('atan', a)                    arctan of the interval
  ('pi',) ('pidiv2',) ('mm1',) ('mm2',)   opaque certified constants
                                 (Machin-pi / cached mm12 enclosures)

Differentiation rules (d/dy_k): mul f'g+fg'; div (f'g-fg')/g^2; sq 2uu';
sqrt(u,tag) u'/(2 sqrt(u,tag)) (shared node); atan(u) u'/(1+u^2).
`fold` applies exact constant folding and x*0/x*1/0+x identities through
an id-keyed memo, so DAG sharing survives.
"""

import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import tmexact as X          # noqa: E402
import dyad                  # noqa: E402
import exprs as EX           # noqa: E402

ONE = ('const', F(1))
ZERO = ('const', F(0))
TWO = ('const', F(2))


def c(fr):
    return ('const', F(fr))


def add(a, b):
    return ('add', a, b)


def sub(a, b):
    return ('sub', a, b)


def mul(a, b):
    return ('mul', a, b)


def neg(a):
    return ('neg', a)


def div(a, b):
    return ('div', a, b)


def sq(a):
    return ('sq', a)


def sqrtN(a, tag=None):
    return ('sqrt', a, tag)


def atan(a):
    return ('atan', a)


# ---------------------------------------------------------------- builder
# Structure mirrors exprs.gamma4_t / jet2.gamma4 (same permutation tables,
# same accumulation order — the tree is the certified image of the same
# pilot expression).

# gamma4 D-term dihedral permutation table (jet2.gamma4 verbatim)
D_PERMS = ((0, 1, 2, 3, 4, 5), (1, 2, 0, 4, 5, 3), (2, 0, 1, 5, 3, 4),
           (3, 2, 4, 0, 5, 1), (4, 0, 5, 1, 3, 2), (5, 0, 4, 2, 3, 1))
# solY permutation table (jet2.gamma4 verbatim)
S_PERMS = ((0, 1, 2, 3, 4, 5), (0, 4, 5, 3, 1, 2), (3, 4, 2, 0, 1, 5),
           (3, 1, 5, 0, 4, 2))


def t_deltaX(perm):
    """deltaX over the permuted x = y^2 (jet2.deltaX verbatim structure)."""
    y = [('var', perm[i]) for i in range(6)]
    x = [sq(v) for v in y]
    x1, x2, x3, x4, x5, x6 = x
    return add(add(add(mul(mul(x1, x4), add(add(add(add(neg(x1), x2), x3),
                                               neg(x4)), add(x5, x6))),
                       mul(mul(x2, x5), add(add(add(add(x1, neg(x2)), x3), x4),
                                            add(neg(x5), x6)))),
                   mul(mul(x3, x6), add(add(add(add(x1, x2), neg(x3)), x4),
                                        add(x5, neg(x6))))),
               neg(add(add(add(mul(mul(x2, x3), x4), mul(mul(x1, x3), x5)),
                           mul(mul(x1, x2), x6)), mul(mul(x4, x5), x6))))


def t_deltaX4(perm):
    """deltaX4 over the permuted x (= y^2) (jet2.deltaX4 verbatim)."""
    y = [('var', perm[i]) for i in range(6)]
    x = [sq(v) for v in y]
    x1, x2, x3, x4, x5, x6 = x
    return add(add(add(add(mul(mul(neg(x2), x3), ONE),
                           neg(mul(x1, x4))),
                       mul(x2, x5)),
                   mul(x3, x6)),
               add(neg(mul(x5, x6)),
                   mul(x1, add(add(add(add(neg(x1), x2), x3), neg(x4)),
                               add(x5, x6)))))


def t_dihY(perm):
    """pi/2 + atan(-deltaX4(x) / sqrt(4 x_{perm0} deltaX(x))), x = y^2.
    The radicand floor is anchored at slot perm[0] (soundness hook 'rad')."""
    x1 = sq(('var', perm[0]))
    rad = mul(mul(('const', F(4)), x1), t_deltaX(perm))
    a = sqrtN(rad, 'rad:%d' % perm[0])
    b = neg(t_deltaX4(perm))
    return add(('pidiv2',), atan(div(b, a)))


def t_solY(perm):
    p = list(perm)
    return sub(add(add(t_dihY((p[0], p[1], p[2], p[3], p[4], p[5])),
                       t_dihY((p[1], p[2], p[0], p[4], p[5], p[3]))),
                   t_dihY((p[2], p[0], p[1], p[5], p[3], p[4]))), ('pi',))


def t_lmfun(i, side):
    """lmfun on one kink side: left = (h0 - y_i/2)/(h0 - 1), right = 0."""
    if side == 'right':
        return ZERO
    h = mul(c(F(1, 2)), ('var', i))
    return div(sub(c(F(63, 50)), h), c(F(13, 50)))


def t_gamma4(sides):
    S = t_solY(S_PERMS[0])
    for pm in S_PERMS[1:]:
        S = add(S, t_solY(pm))
    dterms = None
    for k, pm in enumerate(D_PERMS):
        term = mul(t_lmfun(k, sides[k]), t_dihY(pm))
        dterms = term if dterms is None else add(dterms, term)
    volY = div(sqrtN(t_deltaX((0, 1, 2, 3, 4, 5)), 'delta'), c(12))
    vol4 = sub(mul(div(mul(('const', F(2)), ('mm1',)), ('pi',)), S),
               mul(div(mul(('const', F(8)), ('mm2',)), ('pi',)), dterms))
    return sub(volY, vol4)


def t_main(sides, w, m):
    """main = gamma4/w + m*beta - (a5 + b5*dihY) with b5 = -NEG_B5, i.e.
    gamma4/w + m*beta + (-a5) + NEG_B5*dihY (tmcore.main_jet verbatim)."""
    g = t_gamma4(sides)
    d = t_dihY((0, 1, 2, 3, 4, 5))
    return add(add(div(g, c(w)), c(m * EX.BETA)),
               add(neg(c(EX.A5)), mul(c(EX.NEG_B5), d)))


def t_margin(sides, Bcoef, affine, const):
    """margin = gamma4 + B*dihY + sum c_i y_i + const (affine in order)."""
    g = t_gamma4(sides)
    d = t_dihY((0, 1, 2, 3, 4, 5))
    out = add(g, mul(c(Bcoef), d))
    out = add(out, c(const))
    for k, cf in affine:
        out = add(out, mul(c(cf), ('var', k)))
    return out


# ---------------------------------------------------------------- folding

def fold(t, _cache=None):
    """Exact constant folding + identities, id-memoized (DAG-preserving).
    Shared nodes fold to shared nodes; sqrt tags are preserved."""
    if _cache is None:
        _cache = {}
    got = _cache.get(id(t))
    if got is not None:
        return got
    op = t[0]
    if op == 'const' or len(t) == 1:
        out = t
    elif op == 'neg':
        a = fold(t[1], _cache)
        out = ('neg', a)
    elif op in ('add', 'sub', 'mul', 'div'):
        a = fold(t[1], _cache)
        b = fold(t[2], _cache)
        out = (op, a, b)
        if a[0] == 'const' and b[0] == 'const':
            if op == 'add':
                out = c(a[1] + b[1])
            elif op == 'sub':
                out = c(a[1] - b[1])
            elif op == 'mul':
                out = c(a[1] * b[1])
            elif b[1] != 0:
                out = c(a[1] / b[1])
        elif op == 'add':
            if a[0] == 'const' and a[1] == 0:
                out = b
            elif b[0] == 'const' and b[1] == 0:
                out = a
        elif op == 'sub':
            if b[0] == 'const' and b[1] == 0:
                out = a
        elif op == 'mul':
            if (a[0] == 'const' and a[1] == 0) or \
                    (b[0] == 'const' and b[1] == 0):
                out = ZERO
            elif a[0] == 'const' and a[1] == 1:
                out = b
            elif b[0] == 'const' and b[1] == 1:
                out = a
    elif op == 'sq':
        out = (op, fold(t[1], _cache))
    elif op == 'sqrt':
        out = (op, fold(t[1], _cache), t[2])
    elif op == 'atan':
        out = (op, fold(t[1], _cache))
    else:
        out = t
    _cache[id(t)] = out
    return out


# ---------------------------------------------------------------- derivative

def deriv(t, i, _cache=None):
    """Symbolic d/dy_i (memoized by (id, i); DAG sharing preserved)."""
    if _cache is None:
        _cache = {}
    key = (id(t), i)
    got = _cache.get(key)
    if got is not None:
        return got
    op = t[0]
    if op == 'const' or len(t) == 1:
        out = ZERO
    elif op == 'var':
        out = ONE if t[1] == i else ZERO
    elif op == 'neg':
        out = neg(deriv(t[1], i, _cache))
    elif op == 'add':
        out = add(deriv(t[1], i, _cache), deriv(t[2], i, _cache))
    elif op == 'sub':
        out = sub(deriv(t[1], i, _cache), deriv(t[2], i, _cache))
    elif op == 'mul':
        out = add(mul(deriv(t[1], i, _cache), t[2]),
                  mul(t[1], deriv(t[2], i, _cache)))
    elif op == 'div':
        f, g = t[1], t[2]
        out = div(sub(mul(deriv(f, i, _cache), g), mul(f, deriv(g, i, _cache))),
                  sq(g))
    elif op == 'sq':
        u = t[1]
        out = mul(mul(TWO, u), deriv(u, i, _cache))
    elif op == 'sqrt':
        out = div(deriv(t[1], i, _cache), mul(TWO, t))
    elif op == 'atan':
        out = div(deriv(t[1], i, _cache), add(ONE, sq(t[1])))
    else:
        raise ValueError("deriv: node %r" % (op,))
    _cache[key] = out
    return out


class TreeKit:
    """Per-(pilot, sides) cache: base tree + folded 1st/2nd partials.
    The partial trees are leaf-independent, so they are built once."""

    def __init__(self, base_tree):
        self.base = base_tree
        self._dc = {}
        self._dd = {}
        self.d1 = {}
        self.d2 = {}

    def first(self, i):
        if i not in self.d1:
            self.d1[i] = fold(deriv(self.base, i, self._dc), {})
        return self.d1[i]

    def second(self, i, j):
        if (i, j) not in self.d2:
            di = self.first(i)
            key = (id(di), j)
            t = self._dd.get(key)
            if t is None:
                t = fold(deriv(di, j, self._dd), {})
                self._dd[key] = t
            self.d2[(i, j)] = t
        return self.d2[(i, j)]


# ---------------------------------------------------------------- evaluation

def eval_tree(t, box, N, yboxF, _memo=None):
    """Certified value of the tree over the box (list of Dy) as a Dy.
    `yboxF` is the exact Fraction view of the same box (corner-min data).
    Every operation is a tmexact-backed outward dyadic interval op."""
    if _memo is None:
        _memo = {}
    got = _memo.get(id(t))
    if got is not None:
        return got
    op = t[0]
    if op == 'const':
        out = dyad.Dy.from_frac(t[1], N.coef_grid)
    elif op == 'var':
        out = box[t[1]]
    elif op == 'neg':
        out = -eval_tree(t[1], box, N, yboxF, _memo)
    elif op == 'add':
        out = eval_tree(t[1], box, N, yboxF, _memo) + \
            eval_tree(t[2], box, N, yboxF, _memo)
    elif op == 'sub':
        out = eval_tree(t[1], box, N, yboxF, _memo) - \
            eval_tree(t[2], box, N, yboxF, _memo)
    elif op == 'mul':
        out = eval_tree(t[1], box, N, yboxF, _memo) * \
            eval_tree(t[2], box, N, yboxF, _memo)
    elif op == 'div':
        out = eval_tree(t[1], box, N, yboxF, _memo) / \
            eval_tree(t[2], box, N, yboxF, _memo)
    elif op == 'sq':
        out = eval_tree(t[1], box, N, yboxF, _memo) ** 2
    elif op == 'sqrt':
        v = eval_tree(t[1], box, N, yboxF, _memo)
        if t[2] is not None:
            xbox = tuple((lo * lo, hi * hi) for lo, hi in yboxF)
            cmin = EX.delta_corner_min(xbox)
            if t[2] == 'delta':
                fl = dyad.floor_grid(cmin, N.floor_grid)
            else:                       # 'rad:<k>'
                k = int(t[2].split(':')[1])
                fl = dyad.floor_grid(4 * yboxF[k][0] * cmin, N.floor_grid)
            if X.ble(v.lo, fl):
                v = dyad.Dy(fl, v.hi)
        out = N.sqrt(v)
    elif op == 'atan':
        out = N.atan(eval_tree(t[1], box, N, yboxF, _memo))
    elif op == 'pi':
        out = N.pi()
    elif op == 'pidiv2':
        out = N.pi() / 2
    elif op in ('mm1', 'mm2'):
        EX.mm12(N)                      # ensures the cache
        out = N._mm12[0 if op == 'mm1' else 1]
    else:
        raise ValueError("eval_tree: node %r" % (op,))
    _memo[id(t)] = out
    return out


def eval_main(trees, box, N, yboxF):
    """f over box, resetting the backend sqrt trace; returns (Dy, trace)."""
    N.sqrt_trace = []
    v = eval_tree(trees.base, box, N, yboxF)
    return v, list(N.sqrt_trace)


_KITS = {}


def kit_for(key, base_tree):
    """Memoized TreeKit per (pilot, sides) key — leaf-independent."""
    kit = _KITS.get(key)
    if kit is None:
        kit = TreeKit(base_tree)
        _KITS[key] = kit
    return kit
