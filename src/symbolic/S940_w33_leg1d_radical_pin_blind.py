# -*- coding: utf-8 -*-
# DIM: na (unambiguous pinning of the radicals of the perfect-non-semisimple cores: explicit bracket
#      tables, Heisenberg vs factor split, Levi-module type of the non-central part; 0 handles).
#
# ============================================================================
# CARVE / BRANCH CHOICES (stamped BEFORE any counting)
# ----------------------------------------------------------------------------
# leg-1c pinned each perfect-non-ss core as Levi x| radical.  leg-1d pins the
# RADICAL itself, unambiguously, with an EXPLICIT bracket table in an adapted
# basis (center first), and classifies it through explicit, mutant-guarded
# branches (lesson J-0415: a branch with no mutant is how the (3,2)r0 defect
# slipped through — EVERY branch below carries its own CAUGHT mutant):
#
#   (b) Heisenberg test  h_{2m+1}:  dim Z(rad)=1  AND  dim[rad,rad]=1  AND
#       every non-central x moves ([x,rad]!=0).  -> h{dim}.  Else FACTOR split
#       R^a (+) h^b with a = dimZ - dim[rad,rad], b = dim - a  (abelian center
#       directions beyond the single Heisenberg center are split off).
#       Purely abelian ([rad,rad]=0) -> R^{dim}.
#
#   (c) Module type of the non-central part V = rad/Z under Levi:
#       classified by dim(commutant of the Levi action on V):
#         commutant dim 1  -> ABSOLUTELY IRREDUCIBLE (single irrep of dim=dimV),
#         commutant dim >1 -> REDUCIBLE; the decomposition is EXHIBITED by the
#         minimal cyclic Levi-submodule + the weight multiset of a semisimple
#         Levi element (so a 4-dim V with commutant 4 and weights {+1,+1,-1,-1}
#         is 2(+)2, two copies of the 2-dim; commutant 1 with weights
#         {+3,+1,-1,-3} would be the irreducible 4).
#
# Fences: blindness, exact arithmetic, FORBIDDEN-SCAN, a mutant on EVERY
# classification branch, bit-fence to S933/S935/S937, STOP after the table.
# ============================================================================

import sys
sys.stdout.reconfigure(encoding='utf-8')

import os
import itertools
from math import lcm as _ilcm

from sympy import Matrix, Integer, Rational, zeros, eye, diag, symbols, Poly, gcd, sqrt as ssqrt

X_ = symbols('x')

_LOGPATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "S940_w33_leg1d_radical_pin_blind_run.log")
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


# ==================== primitives (VERBATIM) ====================

def make_eta(p, q):
    return diag(*([Integer(1)] * p + [Integer(-1)] * q))


def unit(n, i):
    v = zeros(n, 1)
    v[i, 0] = Integer(1)
    return v


def wedge(x, y, eta):
    return x * (eta * y).T - y * (eta * x).T


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


def contains(big, small, sq):
    FB = stack_flats(big, sq)
    rb = FB.rank()
    return Matrix.hstack(FB, stack_flats(small, sq)).rank() == rb


def centralizer(A, bas):
    n = A.rows
    cols = [flat(B * A - A * B) for B in bas]
    ns = Matrix.hstack(*cols).nullspace()
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


# ---------- wedge constructors ----------

def d0_on(K, p, n):
    Kp = [a for a in K if a < p]
    Km = [a for a in K if a >= p]
    if len(Kp) >= 2 and len(Km) >= 2:
        return unit(n, Kp[0]) + unit(n, Km[0]), unit(n, Kp[1]) + unit(n, Km[1])
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
    cur = span_basis(L, n)
    while len(cur) > 0:
        nxt = bracket_basis(cur, n)
        if len(nxt) == len(cur):
            return cur
        cur = nxt
    return []


def center_of(cb, n):
    if not cb:
        return []
    cols = []
    for k in range(len(cb)):
        parts = [flat(cb[k] * cb[j] - cb[j] * cb[k]) for j in range(len(cb))]
        cols.append(Matrix.vstack(*parts))
    ns = Matrix.hstack(*cols).nullspace()
    out = []
    for v in ns:
        M = zeros(n, n)
        for k in range(len(cb)):
            if v[k, 0] != 0:
                M = M + v[k, 0] * cb[k]
        out.append(M)
    return span_basis(out, n)


def ad_matrices(L, n):
    k = len(L)
    ads = []
    for i in range(k):
        cols = []
        for j in range(k):
            c = coords_in(L, L[i] * L[j] - L[j] * L[i], n)
            if c is None:
                return None
            cols.append(c)
        ads.append(Matrix.hstack(*cols))
    return ads


def killing_matrix(L, n):
    ads = ad_matrices(L, n)
    if ads is None:
        return None
    k = len(L)
    K = zeros(k, k)
    for i in range(k):
        for j in range(k):
            K[i, j] = (ads[i] * ads[j]).trace()
    return K


def killing_sig(L, n):
    K = killing_matrix(L, n)
    return None if K is None else cong_signature(K)


def n_invforms(L, n):
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
        cols.append(Matrix.vstack(*[flat(a.T * E + E * a) for a in ads]))
    ns = Matrix.hstack(*cols).nullspace()
    return len(ns)


def killing_radical(core, n):
    K = killing_matrix(core, n)
    ns = K.nullspace()
    rad = []
    for v in ns:
        M = zeros(n, n)
        for t in range(len(core)):
            if v[t, 0] != 0:
                M = M + v[t, 0] * core[t]
        rad.append(M)
    return span_basis(rad, n)


def complement_reps(core, rad, n):
    F = stack_flats(rad, n)
    rk = F.rank()
    reps = []
    for M in core:
        F2 = Matrix.hstack(F, flat(M))
        if F2.rank() > rk:
            reps.append(M)
            F = F2
            rk += 1
    return reps


def levi_fp(reps, rad, n):
    # fingerprint of the semisimple quotient core/rad
    full = reps + rad
    kq = len(reps)
    ads = []
    for i in range(kq):
        cols = []
        for j in range(kq):
            co = coords_in(full, reps[i] * reps[j] - reps[j] * reps[i], n)
            cols.append(Matrix(kq, 1, [co[t, 0] for t in range(kq)]))
        ads.append(Matrix.hstack(*cols))
    K = zeros(kq, kq)
    for i in range(kq):
        for j in range(kq):
            K[i, j] = (ads[i] * ads[j]).trace()
    return (kq, cong_signature(K))


def levi_name(reps, rad, n):
    fp = levi_fp(reps, rad, n)
    if fp == (3, (0, 3, 0)):
        return "so(3)"
    if fp == (3, (2, 1, 0)):
        return "so(2,1)"
    return "OTHER" + str(fp)


# ---------- radical structure ----------

def noncentral(rad, Z, n):
    F = stack_flats(Z, n)
    rk = F.rank()
    out = []
    for M in rad:
        F2 = Matrix.hstack(F, flat(M))
        if F2.rank() > rk:
            out.append(M)
            F = F2
            rk += 1
    return out


def classify_radical(rad, n):
    dr = len(rad)
    if dr == 0:
        return "0", dict(dr=0, dz=0, drr=0)
    Z = center_of(rad, n)
    dz = len(Z)
    drr = len(bracket_basis(rad, n))
    nc = noncentral(rad, Z, n)
    allmove = all(len(span_basis([x * r - r * x for r in rad], n)) > 0 for x in nc)
    info = dict(dr=dr, dz=dz, drr=drr, allmove=allmove)
    # BRANCH A: abelian
    if drr == 0:
        return "R%d" % dr, info
    # BRANCH B: Heisenberg h_{2m+1}
    if dz == 1 and drr == 1 and allmove:
        return "h%d" % dr, info
    # BRANCH C: factor split R^a (+) h^b
    a = dz - drr
    b = dr - a
    info["a"] = a
    info["b"] = b
    return "R%d+h%d" % (a, b), info


def adapted_table(rad, n):
    Z = center_of(rad, n)
    Zc = span_basis(Z, n)
    nc = noncentral(rad, Zc, n)
    adapted = Zc + nc
    dz = len(Zc)
    nz = []
    for i in range(len(adapted)):
        for j in range(i + 1, len(adapted)):
            br = adapted[i] * adapted[j] - adapted[j] * adapted[i]
            if not br.is_zero_matrix:
                c = coords_in(adapted, br, n)
                coords = [c[t, 0] for t in range(len(adapted))]
                inZ = all(coords[t] == 0 for t in range(dz, len(adapted)))
                nz.append(((i, j), coords, inZ))
    return dz, len(nc), nz


# ---------- module type of V = rad/Z under Levi ----------

def module_ops(reps, rad, n):
    Z = span_basis(center_of(rad, n), n)
    nc = noncentral(rad, Z, n)
    full = Z + nc
    dz = len(Z)
    dv = len(nc)
    ops = []
    for z in reps:
        cols = []
        for b in range(dv):
            br = z * nc[b] - nc[b] * z
            c = coords_in(full, br, n)
            cols.append(Matrix(dv, 1, [c[dz + t, 0] for t in range(dv)]))
        ops.append(Matrix.hstack(*cols))
    return ops, dv


def commutant_dim(ops, dv):
    eb = end_basis(dv)
    cols = []
    for E in eb:
        cols.append(Matrix.vstack(*[flat(E * op - op * E) for op in ops]))
    return dv * dv - Matrix.hstack(*cols).rank()


def cyclic_dim(v0, ops, dv):
    F = v0.copy()
    r = F.rank()
    frontier = [v0]
    while frontier:
        nf = []
        for w in frontier:
            for op in ops:
                u = op * w
                F2 = Matrix.hstack(F, u)
                if F2.rank() > r:
                    F = F2
                    r += 1
                    nf.append(u)
        frontier = nf
    return r


def min_cyclic_dim(ops, dv):
    best = dv
    for i in range(dv):
        d = cyclic_dim(unit(dv, i), ops, dv)
        if 0 < d < best:
            best = d
    return best


def weight_multiset(ops, dv):
    # eigenvalues of a semisimple (Cartan) Levi element on V — prefer an op with a
    # nonzero, most-split rational spectrum (skip nilpotent ops with all-zero spectrum)
    best = None
    best_score = -1
    for op in ops:
        ev = op.eigenvals()
        if sum(ev.values()) == dv and all(v.is_rational for v in ev.keys()):
            nonzero = any(k != 0 for k in ev.keys())
            score = len(ev) + (100 if nonzero else 0)
            if score > best_score:
                best_score = score
                best = {int(k) if k.is_integer else str(k): int(m) for k, m in ev.items()}
    return best


def module_type(reps, rad, n):
    ops, dv = module_ops(reps, rad, n)
    if dv == 0:
        return "no non-central part", dv, None, None, None
    cdim = commutant_dim(ops, dv)
    wm = weight_multiset(ops, dv)
    if cdim == 1:
        return "irreducible-%d" % dv, dv, cdim, dv, wm
    mcd = min_cyclic_dim(ops, dv)
    return "reducible", dv, cdim, mcd, wm


# ==================== bit-fence tables (S933 / S935 / S937) ====================
FENCE = {
    ("N", 3, 2, "rank0"): dict(dimc=6, derived=[6], core=6, levi="so(2,1)", rad=3, drr=1),
    ("N", 5, 1, "rank1"): dict(dimc=7, derived=[7, 6], core=6, levi="so(3)", rad=3, drr=0),
    ("N", 4, 2, "rank1"): dict(dimc=7, derived=[7, 6], core=6, levi="so(2,1)", rad=3, drr=0),
    ("N", 3, 3, "rank1"): dict(dimc=7, derived=[7, 6], core=6, levi="so(2,1)", rad=3, drr=0),
    ("N", 4, 2, "rank0"): dict(dimc=9, derived=[9, 8], core=8, levi="so(2,1)", rad=5, drr=1),
    ("N", 3, 3, "rank0"): dict(dimc=9, derived=[9, 8], core=8, levi="so(2,1)", rad=5, drr=1),
}

CORES = [
    ("N", 3, 2, "rank0", d0_on),
    ("N", 5, 1, "rank1", d1_on),
    ("N", 4, 2, "rank1", d1_on),
    ("N", 3, 3, "rank1", d1_on),
    ("N", 4, 2, "rank0", d0_on),
    ("N", 3, 3, "rank0", d0_on),
]

print("--- radical pin of the perfect-non-semisimple cores ---")
for (kind, p, q, cls, ctor) in CORES:
    n = p + q
    eta = make_eta(p, q)
    bas = so_basis(n, eta)
    xy = ctor(list(range(n)), p, n)
    N = wedge(xy[0], xy[1], eta)
    c = centralizer(N, bas)
    core = perfect_core(c, n)
    rad = killing_radical(core, n)
    reps = complement_reps(core, rad, n)
    fk = (kind, p, q, cls)
    exp = FENCE[fk]
    # bit-fence to S933/S935/S937
    ok(len(c) == exp["dimc"], "bit-fence dimc " + str(fk))
    ok(derived_series(c, n) == exp["derived"], "bit-fence derived " + str(fk))
    ok(len(core) == exp["core"], "bit-fence core dim " + str(fk))
    ok(len(rad) == exp["rad"], "bit-fence rad dim " + str(fk))
    ok(len(bracket_basis(rad, n)) == exp["drr"], "bit-fence [rad,rad] " + str(fk))
    ok(levi_name(reps, rad, n) == exp["levi"], "bit-fence Levi " + str(fk))
    # classify radical + adapted table
    rtag, info = classify_radical(rad, n)
    dz, dv, nz = adapted_table(rad, n)
    tabstr = "; ".join("[{0},{1}]->{2}{3}".format(ij[0], ij[1],
                                                  [int(x) for x in coords],
                                                  "(inZ)" if inZ else "")
                       for (ij, coords, inZ) in nz) or "(all zero: abelian)"
    mtstr = ""
    if info["drr"] > 0 and dv > 0:
        mt, mdv, cdim, mcd, wm = module_type(reps, rad, n)
        mtstr = " | rad/Z(dim{0}) under Levi: {1} commutant-dim={2} min-cyclic={3} weights={4}".format(
            mdv, mt, cdim, mcd, wm)
    print("CORE ({0},{1}) {2} | core dim={3} Levi={4} | RADICAL={5} (dim={6},dimZ={7},[rad,rad]={8},allmove={9})".format(
        p, q, cls, len(core), levi_name(reps, rad, n), rtag, info["dr"], info["dz"], info["drr"], info.get("allmove")))
    print("     adapted bracket table (Z first, {0} central | {1} non-central): {2}{3}".format(
        dz, dv, tabstr, mtstr))


# ==================== mutants — ONE per classification branch (lesson J-0415) ====================
print("--- mutants (one per classification branch) ---")
mut_ok = True


def build_h5():
    Zc = zeros(4, 4); Zc[0, 3] = Integer(1)
    X1 = zeros(4, 4); X1[0, 1] = Integer(1)
    X2 = zeros(4, 4); X2[0, 2] = Integer(1)
    Y1 = zeros(4, 4); Y1[1, 3] = Integer(1)
    Y2 = zeros(4, 4); Y2[2, 3] = Integer(1)
    return [Zc, X1, X2, Y1, Y2], 4


def build_h3():
    z = zeros(3, 3); z[0, 2] = Integer(1)
    x = zeros(3, 3); x[0, 1] = Integer(1)
    y = zeros(3, 3); y[1, 2] = Integer(1)
    return [z, x, y], 3


def build_R3():
    return [unit(4, 0) * unit(4, 1).T, unit(4, 0) * unit(4, 2).T, unit(4, 0) * unit(4, 3).T], 4


def build_R2h3():
    z = zeros(5, 5); z[0, 2] = Integer(1)
    x = zeros(5, 5); x[0, 1] = Integer(1)
    y = zeros(5, 5); y[1, 2] = Integer(1)
    a = zeros(5, 5); a[3, 3] = Integer(1)
    b = zeros(5, 5); b[4, 4] = Integer(1)
    return [z, a, b, x, y], 5


def build_spin32():
    h = diag(3, 1, -1, -3)
    e = zeros(4, 4); e[0, 1] = Integer(1); e[1, 2] = Integer(2); e[2, 3] = Integer(3)
    f = zeros(4, 4); f[1, 0] = Integer(3); f[2, 1] = Integer(2); f[3, 2] = Integer(1)
    return [h, e, f], 4


def build_2plus2():
    h = diag(1, -1, 1, -1)
    e = zeros(4, 4); e[0, 1] = Integer(1); e[2, 3] = Integer(1)
    f = zeros(4, 4); f[1, 0] = Integer(1); f[3, 2] = Integer(1)
    return [h, e, f], 4


# BRANCH A (abelian R^d)
_r3, _n3 = build_R3()
_ta, _ = classify_radical(_r3, _n3)
if _ta == "R3":
    print("MUTANT br-A (abelian): CAUGHT (R3 -> {0})".format(_ta))
else:
    print("MUTANT br-A: NOT CAUGHT ({0})".format(_ta)); mut_ok = False

# BRANCH B (Heisenberg) -- both h5 and h3
_h5, _nh5 = build_h5()
_h3, _nh3 = build_h3()
_tb5, _ = classify_radical(_h5, _nh5)
_tb3, _ = classify_radical(_h3, _nh3)
if _tb5 == "h5" and _tb3 == "h3":
    print("MUTANT br-B (Heisenberg): CAUGHT (h5->{0}, h3->{1})".format(_tb5, _tb3))
else:
    print("MUTANT br-B: NOT CAUGHT (h5->{0}, h3->{1})".format(_tb5, _tb3)); mut_ok = False

# BRANCH C (factor split R^a (+) h^b)
_rh, _nrh = build_R2h3()
_tc, _ic = classify_radical(_rh, _nrh)
if _tc == "R2+h3" and _ic["dz"] == 3 and _ic["drr"] == 1:
    print("MUTANT br-C (factor split): CAUGHT (R2(+)h3 -> {0}, dimZ={1})".format(_tc, _ic["dz"]))
else:
    print("MUTANT br-C: NOT CAUGHT ({0}, {1})".format(_tc, _ic)); mut_ok = False

# BRANCH module-irreducible (commutant dim 1)
_s32, _ns32 = build_spin32()
_ci = commutant_dim(_s32, 4)
if _ci == 1:
    print("MUTANT br-mod-irred (spin-3/2): CAUGHT (commutant-dim={0})".format(_ci))
else:
    print("MUTANT br-mod-irred: NOT CAUGHT (commutant-dim={0})".format(_ci)); mut_ok = False

# BRANCH module-reducible (commutant dim > 1)
_p22, _np22 = build_2plus2()
_cr = commutant_dim(_p22, 4)
_mc = min_cyclic_dim(_p22, 4)
if _cr == 4 and _mc == 2:
    print("MUTANT br-mod-red (2+2): CAUGHT (commutant-dim={0}, min-cyclic={1})".format(_cr, _mc))
else:
    print("MUTANT br-mod-red: NOT CAUGHT (commutant-dim={0}, min-cyclic={1})".format(_cr, _mc)); mut_ok = False

# GUARD: bracket-table self-consistency rejects a corrupted table
_g3 = eye(3)
_mod3 = span_basis(model_from_constraints(3, [lambda E: E.T * _g3 + _g3 * E]), 3)
_tab3 = sc_table(_mod3, 3)
ok(bt_verify(_mod3, _mod3, _tab3, 3), "guard baseline: uncorrupted table verifies")
_tb = dict(_tab3)
_k0 = sorted(_tb.keys())[0]
_row = list(_tb[_k0]); _row[0] = _row[0] + 1; _tb[_k0] = tuple(_row)
if not bt_verify(_mod3, _mod3, _tb, 3):
    print("MUTANT guard-bt: CAUGHT (bracket-table MISMATCH reported)")
else:
    print("MUTANT guard-bt: NOT CAUGHT"); mut_ok = False


# ==================== sign-fence {eta,-eta} ====================
_p, _q = 4, 2; _n = 6; _eta = make_eta(_p, _q)
_xx, _yy = d0_on(list(range(_n)), _p, _n)
_NN = wedge(_xx, _yy, _eta)
_coreA = perfect_core(centralizer(_NN, so_basis(_n, _eta)), _n)
_coreB = perfect_core(centralizer(_NN, so_basis(_n, -_eta)), _n)
_radA = killing_radical(_coreA, _n)
_radB = killing_radical(_coreB, _n)
ok(classify_radical(_radA, _n)[0] == classify_radical(_radB, _n)[0],
   "sign-fence: radical classification invariant under eta->-eta")
_repsA = complement_reps(_coreA, _radA, _n)
_repsB = complement_reps(_coreB, _radB, _n)
ok(module_type(_repsA, _radA, _n)[2] == module_type(_repsB, _radB, _n)[2],
   "sign-fence: module commutant-dim invariant under eta->-eta")


# ==================== summary ====================
print("SUMMARY: cores_pinned={0}".format(len(CORES)))
print("SUMMARY: asserts_passed={0} | FAIL={1}".format(ASSERT_PASS[0], FAILS[0]))

# ---------- FORBIDDEN-SCAN ----------
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
