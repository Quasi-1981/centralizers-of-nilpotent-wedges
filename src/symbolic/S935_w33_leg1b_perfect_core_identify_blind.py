# -*- coding: utf-8 -*-
# DIM: na (structure table: perfect cores of non-abelian centralizers identified against a fixed menu,
#      plus lower-central/center analysis of the solvable rows; 0 handles — the probe postulates nothing).
#
# ============================================================================
# CARVE CHOICE (stamped BEFORE any counting — first question of leg-1b)
# ----------------------------------------------------------------------------
# leg-1 left c(A) rows tagged sub-of/OTHER against so(p,q).  leg-1b resolves the
# INTERNAL bracket structure of every NON-ABELIAN row (dim[c,c] > 0):
#
#  (1) PERFECT CORE  =  terminal term of the derived series  (iterate [c,c] to
#      stabilization; nonzero => the reductive/semisimple heart).  Identify it
#      SEPARATELY against the menu
#         M = { so(3), so(2,1), sp(2,R), so(4), so(3,1), so(2,2), sp(4,R) }
#      plus all direct sums of pairs from M.
#
#      IDENTIFICATION METHOD (aloud, once): by a COMPLETE bracket-derived
#      isomorphism fingerprint  fp = ( dim , Killing-signature (kp,kq,kz) ,
#      n_invariant_forms ).  The Killing form K(x,y)=tr(ad x ad y) is built from
#      the structure constants (the bracket table); n_invariant_forms = dim of
#      the space of ad-invariant symmetric bilinear forms (an iso-invariant; it
#      equals the number of simple ideals for a split/compact semisimple algebra,
#      but a complex-type simple factor such as sl(2,C)_R contributes 2 — so it
#      is a fingerprint coordinate, not literally an ideal count).  For THIS
#      fixed menu the triple fp separates all non-isomorphic classes by (dim,
#      Killing-sig) alone (checked: models carry pairwise-distinct fp except
#      genuine isomorphs so(2,1)==sp(2,R), so(4)==so(3)+so(3),
#      so(2,2)==so(2,1)+so(2,1) — reported with '&').  A match is only accepted
#      after bt_verify (S929) confirms the model's own bracket table is
#      self-consistent.  No fp match => OTHER (honest; e.g. dim not on the menu).
#
#  (2) SOLVABLE rows (derived series reaches 0): columns = lower-central
#      (nilpotent) series, dim center at each level, derived series; and the
#      named question — are the (4,1) and (3,2) rank-1 rows isomorphic — decided
#      by the disc-form signature of ad(L) acting on [L,L] (a conjugation
#      invariant: elliptic ±i vs hyperbolic ±1 cannot be exchanged by a real
#      Lie isomorphism).
#
# Same fences as leg-1: blindness, exact arithmetic, mutants, FORBIDDEN-SCAN,
# and a bit-fence to S933 (every row's dimc/derived re-derived and asserted).
# ============================================================================

import sys
sys.stdout.reconfigure(encoding='utf-8')

import os
import itertools
from math import lcm as _ilcm

from sympy import Matrix, Integer, Rational, zeros, eye, diag, symbols, Poly, gcd, sqrt as ssqrt

X_ = symbols('x')

_LOGPATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "S935_w33_leg1b_perfect_core_identify_blind_run.log")
_logf = open(_LOGPATH, "w", encoding="utf-8")


class Tee:
    def __init__(self, real, fh):
        self.real = real
        self.fh = fh
        self.chunks = []

    def write(self, s):
        self.real.write(s)
        self.fh.write(s)
        self.chunks.append(s)
        return len(s)

    def flush(self):
        self.real.flush()
        if not self.fh.closed:
            self.fh.flush()


_tee = Tee(sys.stdout, _logf)
sys.stdout = _tee

ASSERT_PASS = [0]
FAILS = [0]


def ok(cond, msg):
    if cond:
        ASSERT_PASS[0] += 1
    else:
        FAILS[0] += 1
        print("ASSERT-FAIL: " + msg)


# ==================== primitives (VERBATIM from S929/S933) ====================

def make_eta(p, q):
    return diag(*([Integer(1)] * p + [Integer(-1)] * q))


def unit(n, i):
    v = zeros(n, 1)
    v[i, 0] = Integer(1)
    return v


def wedge(x, y, eta):
    return x * (eta * y).T - y * (eta * x).T


def is_so(M, eta):
    return (M.T * eta + eta * M).is_zero_matrix


def so_basis(n, eta):
    out = []
    for i in range(n):
        for j in range(i + 1, n):
            out.append(wedge(unit(n, i), unit(n, j), eta))
    return out


def flat(M):
    n = M.rows
    return Matrix(n * n, 1, list(M))


def stack_flats(mats, sq):
    if not mats:
        return zeros(sq * sq, 0)
    return Matrix.hstack(*[flat(M) for M in mats])


def span_rank(mats, sq):
    return stack_flats(mats, sq).rank()


def span_basis(mats, sq):
    out = []
    F = zeros(sq * sq, 0)
    r = 0
    for M in mats:
        F2 = Matrix.hstack(F, flat(M))
        if F2.rank() > r:
            out.append(M)
            F = F2
            r += 1
    return out


def same_span(A, B, sq):
    FA = stack_flats(A, sq)
    FB = stack_flats(B, sq)
    ra = FA.rank()
    rb = FB.rank()
    if ra != rb:
        return False
    return Matrix.hstack(FA, FB).rank() == ra


def contains(big, small, sq):
    FB = stack_flats(big, sq)
    rb = FB.rank()
    return Matrix.hstack(FB, stack_flats(small, sq)).rank() == rb


def centralizer(A, bas):
    n = A.rows
    cols = [flat(B * A - A * B) for B in bas]
    Mmap = Matrix.hstack(*cols)
    ns = Mmap.nullspace()
    cb = []
    for v in ns:
        M = zeros(n, n)
        for k in range(len(bas)):
            if v[k, 0] != 0:
                M = M + v[k, 0] * bas[k]
        cb.append(M)
    return cb


def is_nilp(A):
    n = A.rows
    A2 = A * A
    if A2.is_zero_matrix:
        return True
    if A2.trace() != 0:
        return False
    return (A ** n).is_zero_matrix


def squarefree(mp):
    me = mp.as_expr()
    g = gcd(me, me.diff(X_))
    return Poly(g, X_).degree() == 0


def minpoly_poly(A):
    n = A.rows
    pows = [eye(n)]
    for _k in range(n):
        pows.append(pows[-1] * A)
    flats = [flat(P) for P in pows]
    for d in range(1, n + 1):
        Mstack = Matrix.hstack(*flats[:d])
        v = flats[d]
        if Matrix.hstack(Mstack, v).rank() == Mstack.rank():
            sol, params = Mstack.gauss_jordan_solve(v)
            if params.rows * params.cols > 0:
                sol = sol.subs({s: 0 for s in params})
            expr = X_ ** d
            for k in range(d):
                expr = expr - sol[k, 0] * X_ ** k
            return Poly(expr, X_)
    return Poly(X_ ** n, X_)


def gram2(x, y, eta):
    a = (x.T * eta * x)[0, 0]
    b = (x.T * eta * y)[0, 0]
    c = (y.T * eta * y)[0, 0]
    return Matrix([[a, b], [b, c]])


def block_gen(n, eta, i, j, param):
    return Integer(param) * wedge(unit(n, i), unit(n, j), eta)


def cong_signature(Gin):
    G = Gin.copy()
    pos = neg = zer = 0
    while G.rows > 0:
        m = G.rows
        k = None
        for i in range(m):
            if G[i, i] != 0:
                k = i
                break
        if k is None:
            pair = None
            for i in range(m):
                for j in range(i + 1, m):
                    if G[i, j] != 0:
                        pair = (i, j)
                        break
                if pair is not None:
                    break
            if pair is None:
                zer += m
                break
            i, j = pair
            G[i, :] = G[i, :] + G[j, :]
            G[:, i] = G[:, i] + G[:, j]
            continue
        dv = G[k, k]
        if dv > 0:
            pos += 1
        else:
            neg += 1
        v = G[:, k]
        G = G - (v * v.T) / dv
        G.row_del(k)
        G.col_del(k)
    return (pos, neg, zer)


def coords_in(basis, M, sq):
    F = stack_flats(basis, sq)
    v = flat(M)
    if F.cols == 0:
        return None if not v.is_zero_matrix else Matrix(0, 1, [])
    try:
        sol, params = F.gauss_jordan_solve(v)
    except ValueError:
        return None
    if params.rows * params.cols > 0:
        sol = sol.subs({s: 0 for s in params})
    if not (F * sol - v).is_zero_matrix:
        return None
    return sol


def sc_table(basis, sq):
    tab = {}
    for i in range(len(basis)):
        for j in range(i + 1, len(basis)):
            br = basis[i] * basis[j] - basis[j] * basis[i]
            c = coords_in(basis, br, sq)
            if c is None:
                return None
            tab[(i, j)] = tuple(c)
    return tab


def bt_verify(L, Mo, mtable, sq):
    k = len(L)
    if k == 0:
        return True
    if mtable is None:
        return False
    A = [coords_in(Mo, L[i], sq) for i in range(k)]
    if any(a is None for a in A):
        return False
    B = [coords_in(L, Mo[g], sq) for g in range(len(Mo))]
    if any(b is None for b in B):
        return False
    Ltab = sc_table(L, sq)
    if Ltab is None:
        return False
    km = len(Mo)
    for i in range(k):
        for j in range(i + 1, k):
            pv = [Integer(0)] * km
            for a in range(km):
                for b in range(km):
                    if a == b:
                        continue
                    coef = A[i][a] * A[j][b]
                    if coef == 0:
                        continue
                    if a < b:
                        f = mtable[(a, b)]
                        sgn = 1
                    else:
                        f = mtable[(b, a)]
                        sgn = -1
                    for g in range(km):
                        pv[g] = pv[g] + sgn * coef * f[g]
            pl = [Integer(0)] * k
            for g in range(km):
                if pv[g] != 0:
                    for t in range(k):
                        pl[t] = pl[t] + pv[g] * B[g][t]
            direct = Ltab[(i, j)]
            if any(pl[t] != direct[t] for t in range(k)):
                return False
    return True


def end_basis(d):
    out = []
    for i in range(d):
        for j in range(d):
            E = zeros(d, d)
            E[i, j] = Integer(1)
            out.append(E)
    return out


def model_from_constraints(d, cons):
    eb = end_basis(d)
    cols = []
    for E in eb:
        parts = [flat(fn(E)) for fn in cons]
        cols.append(Matrix.vstack(*parts))
    ns = Matrix.hstack(*cols).nullspace()
    out = []
    for v in ns:
        M = zeros(d, d)
        for k in range(d * d):
            if v[k, 0] != 0:
                M = M + v[k, 0] * eb[k]
        out.append(M)
    return out


def model_sp_w(w):
    d = w.rows
    return model_from_constraints(d, [lambda E: E.T * w + w * E])


# ---------- wedge constructors (S933 conventions) ----------

def d0_on(K, p, n):
    Kp = [a for a in K if a < p]
    Km = [a for a in K if a >= p]
    if len(Kp) >= 2 and len(Km) >= 2:
        x = unit(n, Kp[0]) + unit(n, Km[0])
        y = unit(n, Kp[1]) + unit(n, Km[1])
        return x, y
    return None


def d1_on(K, p, n):
    Kp = [a for a in K if a < p]
    Km = [a for a in K if a >= p]
    if len(Kp) >= 1 and len(Km) >= 1 and len(K) >= 3:
        a, b = Kp[0], Km[0]
        rest = [c for c in K if c not in (a, b)]
        c = rest[0]
        return unit(n, a) + unit(n, b), unit(n, c)
    return None


def q_gram(cb):
    d = len(cb)
    G = zeros(d, d)
    for a in range(d):
        for b in range(a, d):
            t = (cb[a] * cb[b]).trace()
            G[a, b] = t
            G[b, a] = t
    return G


def jordan_scan(cb, G, n):
    d = len(cb)
    dens = []
    for i in range(d):
        for j in range(d):
            dens.append(int(G[i, j].q))
    Lc = 1
    for de in dens:
        Lc = _ilcm(Lc, de)
    Gi = [[int(G[i, j] * Lc) for j in range(d)] for i in range(d)]
    vals = (-2, -1, 0, 1, 2)
    for c in itertools.product(vals, repeat=d):
        if all(x == 0 for x in c):
            continue
        s = 0
        for i in range(d):
            ci = c[i]
            if ci:
                row = Gi[i]
                s += ci * sum(row[j] * c[j] for j in range(d))
        if s != 0:
            continue
        Xm = zeros(n, n)
        for k in range(d):
            if c[k]:
                Xm = Xm + Integer(c[k]) * cb[k]
        if Xm.is_zero_matrix:
            continue
        if is_nilp(Xm):
            return Xm
    return None


def sig_list():
    out = []
    for n in (4, 5, 6):
        for q in range(0, n // 2 + 1):
            p = n - q
            if p >= q:
                out.append((p, q))
    return out


# ==================== NEW leg-1b structure machinery ====================

def bracket_basis(L, n):
    brs = []
    for a in range(len(L)):
        for b in range(a + 1, len(L)):
            brs.append(L[a] * L[b] - L[b] * L[a])
    return span_basis(brs, n)


def derived_series(L, n):
    cur = span_basis(L, n)
    dims = [len(cur)]
    while len(cur) > 0:
        nxt = bracket_basis(cur, n)
        if len(nxt) == len(cur):
            break
        dims.append(len(nxt))
        cur = nxt
    return dims


def perfect_core(L, n):
    # terminal term of the derived series: [] if solvable (reaches 0), else the perfect subalgebra
    cur = span_basis(L, n)
    while len(cur) > 0:
        nxt = bracket_basis(cur, n)
        if len(nxt) == len(cur):
            return cur
        cur = nxt
    return []


def lower_central_series(L, n):
    # L_1 = L, L_{k+1} = [L, L_k]; dims to stabilization
    L0 = span_basis(L, n)
    cur = L0
    dims = [len(cur)]
    while len(cur) > 0:
        brs = []
        for a in range(len(L0)):
            for b in range(len(cur)):
                brs.append(L0[a] * cur[b] - cur[b] * L0[a])
        nxt = span_basis(brs, n)
        if len(nxt) == len(cur):
            break
        dims.append(len(nxt))
        cur = nxt
    return dims


def lower_central_terms(L, n):
    L0 = span_basis(L, n)
    cur = L0
    terms = [cur]
    while len(cur) > 0:
        brs = []
        for a in range(len(L0)):
            for b in range(len(cur)):
                brs.append(L0[a] * cur[b] - cur[b] * L0[a])
        nxt = span_basis(brs, n)
        if len(nxt) == len(cur):
            break
        terms.append(nxt)
        cur = nxt
    return terms


def center_of(cb, n):
    if not cb:
        return []
    cols = []
    for k in range(len(cb)):
        parts = [flat(cb[k] * cb[j] - cb[j] * cb[k]) for j in range(len(cb))]
        cols.append(Matrix.vstack(*parts))
    Mmap = Matrix.hstack(*cols)
    ns = Mmap.nullspace()
    out = []
    for v in ns:
        M = zeros(n, n)
        for k in range(len(cb)):
            if v[k, 0] != 0:
                M = M + v[k, 0] * cb[k]
        out.append(M)
    return span_basis(out, n)


def ad_matrices(L, n):
    # ad(e_i) as k x k matrix in the basis L (column j = coords of [e_i,e_j])
    k = len(L)
    ads = []
    for i in range(k):
        cols = []
        for j in range(k):
            br = L[i] * L[j] - L[j] * L[i]
            c = coords_in(L, br, n)
            if c is None:
                return None
            cols.append(c)
        ads.append(Matrix.hstack(*cols))
    return ads


def killing_sig(L, n):
    ads = ad_matrices(L, n)
    if ads is None:
        return None
    k = len(L)
    K = zeros(k, k)
    for i in range(k):
        for j in range(k):
            K[i, j] = (ads[i] * ads[j]).trace()
    return cong_signature(K)


def n_invforms(L, n):
    # number of ad-invariant symmetric bilinear forms = # simple ideals (semisimple case)
    ads = ad_matrices(L, n)
    if ads is None:
        return None
    k = len(L)
    symb = []
    for i in range(k):
        for j in range(i, k):
            E = zeros(k, k)
            E[i, j] = Integer(1)
            E[j, i] = Integer(1)
            symb.append(E)
    cols = []
    for E in symb:
        parts = [flat(a.T * E + E * a) for a in ads]
        cols.append(Matrix.vstack(*parts))
    ns = Matrix.hstack(*cols).nullspace()
    return len(ns)


def fingerprint(L, n):
    b = span_basis(L, n)
    dim = len(b)
    ks = killing_sig(b, n)
    ni = n_invforms(b, n)
    return (dim, ks, ni)


# ---------- fixed menu + all pair direct sums (fp is additive over direct sum) ----------

def sp_form(m):
    J = zeros(2 * m, 2 * m)
    for i in range(m):
        J[i, m + i] = Integer(1)
        J[m + i, i] = Integer(-1)
    return J


MENU_DEFS = [
    ("so(3)",   so_basis(3, make_eta(3, 0)), 3),
    ("so(2,1)", so_basis(3, make_eta(2, 1)), 3),
    ("sp(2,R)", model_sp_w(sp_form(1)),      2),
    ("so(4)",   so_basis(4, make_eta(4, 0)), 4),
    ("so(3,1)", so_basis(4, make_eta(3, 1)), 4),
    ("so(2,2)", so_basis(4, make_eta(2, 2)), 4),
    ("sp(4,R)", model_sp_w(sp_form(2)),      4),
]

MENU_FP = []   # (name, fp)
print("--- menu base fingerprints (dim, Killing-sig(pos,neg,zer), n_invforms) ---")
for (nm, bas0, nn) in MENU_DEFS:
    b = span_basis(bas0, nn)
    fp = fingerprint(b, nn)
    # sanity: perfect + semisimple + self-consistent bracket table
    ok(len(bracket_basis(b, nn)) == len(b), "menu perfect " + nm)
    ok(fp[1][2] == 0, "menu semisimple (Killing nondeg) " + nm)
    ok(bt_verify(b, b, sc_table(b, nn), nn), "menu bracket-table self-consistent " + nm)
    MENU_FP.append((nm, fp))
    print("MENU {0}: dim={1} Killing={2} n_invforms={3}".format(nm, fp[0], fp[1], fp[2]))


def fp_add(a, b):
    return (a[0] + b[0],
            (a[1][0] + b[1][0], a[1][1] + b[1][1], a[1][2] + b[1][2]),
            a[2] + b[2])


CATALOG = list(MENU_FP)   # singles
for i in range(len(MENU_FP)):
    for j in range(i, len(MENU_FP)):
        ni, fi = MENU_FP[i]
        nj, fj = MENU_FP[j]
        CATALOG.append((ni + "+" + nj, fp_add(fi, fj)))


def identify_core(core, n):
    fp = fingerprint(core, n)
    names = [nm for (nm, f) in CATALOG if f == fp]
    if names:
        return "match=" + "&".join(names) + ":dim{0}:Killing{1}:ninv{2}".format(fp[0], fp[1], fp[2])
    return "OTHER:dim{0}:Killing{1}:ninv{2}".format(fp[0], fp[1], fp[2])


# ---------- disc-form signature of ad(L) acting on an ideal (metabelian rows) ----------

def rho_on(L, W, n):
    # span of { ad(z)|_W : z in L } inside gl(W) (W an L-invariant ideal, dim(W)=w)
    w = len(W)
    ops = []
    for z in L:
        cols = []
        for b in range(w):
            br = z * W[b] - W[b] * z
            c = coords_in(W, br, n)
            if c is None:
                return None
            cols.append(c)
        ops.append(Matrix.hstack(*cols))
    return span_basis(ops, w)


def disc_form_sig(rho):
    # rho: basis (r matrices, each w x w with w=2) of a commutative subalgebra of gl(2);
    # Q(c) = tr(sum c_k A_k)^2 - 4 det(...) is a quadratic form on the coefficients -> its congruence signature
    r = len(rho)
    if r == 0:
        return (0, 0, 0)
    cs = symbols('c0:%d' % r)
    M = zeros(2, 2)
    for k in range(r):
        M = M + cs[k] * rho[k]
    Q = (M.trace() ** 2 - 4 * M.det()).expand()
    S = zeros(r, r)
    for a in range(r):
        for b in range(r):
            if a == b:
                S[a, b] = Q.coeff(cs[a], 2)
            else:
                co = Q.coeff(cs[a], 1).coeff(cs[b], 1)
                S[a, b] = Rational(co, 2)
    return cong_signature(S)


# ==================== bit-fence to S933 (dimc, derived) ====================
# expected (dimc, derived-series) captured from the S933 run
FENCE933 = {
    ("N", 3, 1, "rank1"): (2, [2, 0]),
    ("N", 2, 2, "rank0"): (4, [4, 3]),
    ("N", 2, 2, "rank1"): (2, [2, 0]),
    ("N", 4, 1, "rank1"): (4, [4, 2, 0]),
    ("N", 3, 2, "rank0"): (6, [6]),
    ("N", 3, 2, "rank1"): (4, [4, 2, 0]),
    ("N", 5, 1, "rank1"): (7, [7, 6]),
    ("N", 4, 2, "rank0"): (9, [9, 8]),
    ("N", 4, 2, "rank1"): (7, [7, 6]),
    ("N", 3, 3, "rank0"): (9, [9, 8]),
    ("N", 3, 3, "rank1"): (7, [7, 6]),
    ("J1",): (2, [2, 0]),
    ("J2",): (5, [5, 3]),
    ("J3",): (3, [3, 0]),
    ("J4",): (5, [5, 3]),
}

ROWS = [0]
SOLVABLE = {}   # key -> (L, n) for the named iso comparison


def classify_and_print(kind, p, q, cls, L, n, fence_key):
    ok(all(is_so(M, make_eta(p, q)) for M in L), "c-basis in so " + str(fence_key))
    dser = derived_series(L, n)
    dcc = dser[1] if len(dser) > 1 else 0
    # bit-fence
    exp_dc, exp_dser = FENCE933[fence_key]
    ok(len(L) == exp_dc, "bit-fence dimc " + str(fence_key))
    ok(dser == exp_dser, "bit-fence derived " + str(fence_key))
    ROWS[0] += 1
    if dcc == 0:
        print("ROW {0} SIG=({1},{2}) {3} | dimc={4} | ABELIAN (dim[c,c]=0) | derived={5} | dimZ={6}".format(
            kind, p, q, cls, len(L), dser, len(center_of(L, n))))
        return
    core = perfect_core(L, n)
    if core:
        ok(len(bracket_basis(core, n)) == len(core), "core perfect " + str(fence_key))
        ident = identify_core(core, n)
        print("ROW {0} SIG=({1},{2}) {3} | dimc={4} | NON-ABELIAN | derived={5} | perfect-core dim={6} | CORE-ID={7}".format(
            kind, p, q, cls, len(L), dser, len(core), ident))
    else:
        # solvable: lower-central series + center per level
        lcs = lower_central_series(L, n)
        terms = lower_central_terms(L, n)
        zlv = [len(center_of(T, n)) for T in terms]
        print("ROW {0} SIG=({1},{2}) {3} | dimc={4} | SOLVABLE | derived={5} | lower-central={6} | center-per-lcs-level={7}".format(
            kind, p, q, cls, len(L), dser, lcs, zlv))
        SOLVABLE[(p, q, cls)] = (L, n)


# ---- part 1: nilpotent rows ----
print("--- part 1: perfect-core / solvable structure of nilpotent-row centralizers ---")
for (p, q) in sig_list():
    n = p + q
    eta = make_eta(p, q)
    bas = so_basis(n, eta)
    for (cls, ctor) in (("rank0", d0_on), ("rank1", d1_on)):
        xy = ctor(list(range(n)), p, n)
        if xy is None:
            continue
        x, y = xy
        N = wedge(x, y, eta)
        ok(is_nilp(N), "N nilpotent ({0},{1}) {2}".format(p, q, cls))
        L = centralizer(N, bas)
        classify_and_print("N", p, q, cls, L, n, ("N", p, q, cls))

# ---- part 2: mixed rows J1-J4 ----
print("--- part 2: perfect-core structure of mixed-row centralizers ---")

# J1 (2,2)
_p, _q = 2, 2; _n = 4; _eta = make_eta(_p, _q); _bas = so_basis(_n, _eta)
_S = block_gen(_n, _eta, 0, 2, 1) + block_gen(_n, _eta, 1, 3, 1)
_cbS = centralizer(_S, _bas)
_N = jordan_scan(_cbS, q_gram(_cbS), _n)
_A = _S + _N
classify_and_print("J1", _p, _q, "mixed", centralizer(_A, _bas), _n, ("J1",))

# J2 (4,2)
_p, _q = 4, 2; _n = 6; _eta = make_eta(_p, _q); _bas = so_basis(_n, _eta)
_S = block_gen(_n, _eta, 0, 1, 1)
_x, _y = d0_on([2, 3, 4, 5], _p, _n)
_A = _S + wedge(_x, _y, _eta)
classify_and_print("J2", _p, _q, "mixed", centralizer(_A, _bas), _n, ("J2",))

# J3 (5,1)
_p, _q = 5, 1; _n = 6; _eta = make_eta(_p, _q); _bas = so_basis(_n, _eta)
_S = block_gen(_n, _eta, 0, 1, 1)
_x, _y = d1_on([2, 3, 4, 5], _p, _n)
_A = _S + wedge(_x, _y, _eta)
classify_and_print("J3", _p, _q, "mixed", centralizer(_A, _bas), _n, ("J3",))

# J4 (3,3)
_p, _q = 3, 3; _n = 6; _eta = make_eta(_p, _q); _bas = so_basis(_n, _eta)
_S = block_gen(_n, _eta, 0, _p, 1)
_x, _y = d0_on([1, 2, 4, 5], _p, _n)
_A = _S + wedge(_x, _y, _eta)
classify_and_print("J4", _p, _q, "mixed", centralizer(_A, _bas), _n, ("J4",))


# ==================== named question: (4,1) rank1  vs  (3,2) rank1 ====================
print("--- named: are (4,1) rank1 and (3,2) rank1 centralizers isomorphic? ---")
ISO_RESULT = None
if (4, 1, "rank1") in SOLVABLE and (3, 2, "rank1") in SOLVABLE:
    L1, n1 = SOLVABLE[(4, 1, "rank1")]
    L2, n2 = SOLVABLE[(3, 2, "rank1")]
    W1 = bracket_basis(L1, n1)
    W2 = bracket_basis(L2, n2)
    ok(len(bracket_basis(W1, n1)) == 0, "[L,L] abelian (4,1)")
    ok(len(bracket_basis(W2, n2)) == 0, "[L,L] abelian (3,2)")
    r1 = rho_on(L1, W1, n1)
    r2 = rho_on(L2, W2, n2)
    s1 = disc_form_sig(r1)
    s2 = disc_form_sig(r2)
    # full battery
    b1 = (len(L1), derived_series(L1, n1), lower_central_series(L1, n1),
          len(center_of(L1, n1)), len(W1), len(r1), s1)
    b2 = (len(L2), derived_series(L2, n2), lower_central_series(L2, n2),
          len(center_of(L2, n2)), len(W2), len(r2), s2)
    iso = (b1 == b2)
    ISO_RESULT = "ISOMORPHIC" if iso else "DISTINCT"
    print("(4,1)r1 battery: dimL={0} derived={1} lower-central={2} dimZ={3} dim[L,L]={4} dim-rho={5} disc-form-sig={6}".format(*b1))
    print("(3,2)r1 battery: dimL={0} derived={1} lower-central={2} dimZ={3} dim[L,L]={4} dim-rho={5} disc-form-sig={6}".format(*b2))
    print("VERDICT (by bracket-derived conjugation invariant of ad on [L,L]): {0} (disc-form-sig {1} vs {2})".format(
        ISO_RESULT, s1, s2))


# ==================== mutants — each a REAL new code path, must be CAUGHT ====================
print("--- mutants ---")
mut_ok = True

# mu1: perfect_core separates perfect from solvable
_pc_perf = perfect_core(so_basis(3, make_eta(2, 1)), 3)     # so(2,1) is perfect -> returns itself (dim 3)
_Hs = Matrix([[Integer(1), 0], [0, Integer(-1)]])
_Es = Matrix([[0, Integer(1)], [0, 0]])
_pc_solv = perfect_core([_Hs, _Es], 2)                       # aff(1) solvable -> []
ok(len(_pc_perf) == 3, "mu1 baseline: perfect_core(so(2,1))=dim3")
ok(len(_pc_solv) == 0, "mu1 baseline: perfect_core(aff(1))=empty")
if len(_pc_perf) == 3 and len(_pc_solv) == 0:
    print("MUTANT mu1: CAUGHT (perfect_core separates perfect dim3 from solvable empty)")
else:
    print("MUTANT mu1: NOT CAUGHT")
    mut_ok = False

# mu2: Killing signature separates compact so(3) from split so(2,1)
_ks3 = killing_sig(so_basis(3, make_eta(3, 0)), 3)
_ks21 = killing_sig(so_basis(3, make_eta(2, 1)), 3)
ok(_ks3[2] == 0 and _ks21[2] == 0, "mu2 baseline: both semisimple")
if _ks3 != _ks21:
    print("MUTANT mu2: CAUGHT (Killing sig separates so(3)={0} from so(2,1)={1})".format(_ks3, _ks21))
else:
    print("MUTANT mu2: NOT CAUGHT")
    mut_ok = False

# mu3: n_invforms counts simple ideals (1 for so(3), 2 for so(3)+so(3)=so(4))
_ni_simple = n_invforms(so_basis(3, make_eta(3, 0)), 3)
_ni_so4 = n_invforms(so_basis(4, make_eta(4, 0)), 4)
ok(_ni_simple == 1, "mu3 baseline: n_invforms(so(3))=1")
if _ni_simple == 1 and _ni_so4 == 2:
    print("MUTANT mu3: CAUGHT (n_invforms counts ideals: so(3)=1, so(4)=2)")
else:
    print("MUTANT mu3: NOT CAUGHT (so4={0})".format(_ni_so4))
    mut_ok = False

# mu4: disc-form signature separates rotation (elliptic) from boost (hyperbolic)
_J = Matrix([[0, Integer(-1)], [Integer(1), 0]])       # rotation, eigenvalues +-i
_Bst = Matrix([[Integer(1), 0], [0, Integer(-1)]])     # boost, eigenvalues +-1
_sig_rot = disc_form_sig([_J])
_sig_boost = disc_form_sig([_Bst])
ok(_sig_rot[1] == 1 and _sig_rot[0] == 0, "mu4 baseline: rotation disc-form negative")
ok(_sig_boost[0] == 1 and _sig_boost[1] == 0, "mu4 baseline: boost disc-form positive")
if _sig_rot != _sig_boost:
    print("MUTANT mu4: CAUGHT (disc-form sig separates rotation {0} from boost {1})".format(_sig_rot, _sig_boost))
else:
    print("MUTANT mu4: NOT CAUGHT")
    mut_ok = False

# mu5: bracket-table self-consistency (reused bt_verify) rejects a corrupted table
_g3 = eye(3)
_mod3 = span_basis(model_from_constraints(3, [lambda E: E.T * _g3 + _g3 * E]), 3)
_tab3 = sc_table(_mod3, 3)
ok(bt_verify(_mod3, _mod3, _tab3, 3), "mu5 baseline: uncorrupted table verifies")
_tb = dict(_tab3)
_k0 = sorted(_tb.keys())[0]
_row = list(_tb[_k0])
_row[0] = _row[0] + 1
_tb[_k0] = tuple(_row)
if not bt_verify(_mod3, _mod3, _tb, 3):
    print("MUTANT mu5: CAUGHT (bracket-table MISMATCH reported)")
else:
    print("MUTANT mu5: NOT CAUGHT")
    mut_ok = False


# ==================== sign-fence {eta, -eta} on a representative row ====================
_p, _q = 4, 2
_n = 6
_eta = make_eta(_p, _q)
_x, _y = d0_on(list(range(_n)), _p, _n)
_N = wedge(_x, _y, _eta)
_cA = perfect_core(centralizer(_N, so_basis(_n, _eta)), _n)
_cB = perfect_core(centralizer(_N, so_basis(_n, -_eta)), _n)
ok(fingerprint(_cA, _n) == fingerprint(_cB, _n), "sign-fence: core fingerprint invariant under eta -> -eta")


# ==================== summary ====================
print("SUMMARY: rows={0} | menu_singles={1} | catalog_entries={2}".format(ROWS[0], len(MENU_FP), len(CATALOG)))
print("SUMMARY: named-iso (4,1)r1 vs (3,2)r1 = {0}".format(ISO_RESULT))
print("SUMMARY: asserts_passed={0} | FAIL={1}".format(ASSERT_PASS[0], FAILS[0]))

# ---------- FORBIDDEN-SCAN (same mechanism as S929/S933) ----------
_pieces = [("з", "акон"), ("к", "анал"), ("мех", "анізм"), ("зл", "іпок"),
           ("пер", "егин"), ("конд", "енсат"), ("мат", "ерія"), ("ен", "ергія"),
           ("рез", "онанс"), ("тр", "іщина"), ("г", "учн")]
_words = ["".join(ab).casefold() for ab in _pieces]
_src = open(__file__, "r", encoding="utf-8").read().casefold()
_logf.flush()
_logtxt = "".join(_tee.chunks).casefold()
_hits = 0
for _w2 in _words:
    if _w2 in _src:
        _hits += 1
    if _w2 in _logtxt:
        _hits += 1
print("FORBIDDEN-SCAN: hits={0}".format(_hits))

_exit = 0
if _hits > 0:
    _exit = 1
if FAILS[0] > 0:
    _exit = 1
if not mut_ok:
    _exit = 1
print("EXIT={0}".format(_exit))
sys.stdout = _tee.real
_logf.close()
sys.exit(_exit)
