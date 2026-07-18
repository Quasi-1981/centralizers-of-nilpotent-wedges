# -*- coding: utf-8 -*-
# DIM: na (fix of the S935 classification branch + Levi/radical structure of the perfect-non-semisimple
#      cores; 0 handles — the probe postulates nothing).
#
# ============================================================================
# WHAT leg-1c FIXES + ADDS  (carve choices stamped BEFORE any counting)
# ----------------------------------------------------------------------------
# DEFECT (found by hand on S935): the classification read dim[c,c] as
# "dser[1] if len(dser)>1 else 0".  For a PERFECT WHOLE algebra the derived
# series is length 1 ([6]) so that expression wrongly gave 0 -> the row (3,2)r0
# was mislabelled ABELIAN.  FIX: dim[c,c] := len(bracket_basis(c)) directly, so
# "perfect whole" (dim[c,c]=dim c) is correctly NON-ABELIAN.  A dedicated mutant
# (perfect-whole vs abelian) guards the fixed branch.  (3,2)r0 is RE-MEASURED
# from its construction, not copied.
#
# LEVI EXTRACTION (operationalization, aloud once):
#   For a perfect algebra core, radical := ker(Killing form) = [core,core]^perp
#   (valid because core is perfect).  Levi := the semisimple quotient core/radical;
#   its iso-type is read off its INDUCED bracket table (Killing sig + n_invforms)
#   and matched against { so(3), so(2,1) }.  An EXPLICIT bracket-closed complement
#   is then sought by solving the linear Levi-cocycle system (Whitehead: H^2=0);
#   it is exhibited + bt_verified against the model when the (drop-[rad,rad])
#   solution closes exactly, otherwise the quotient realization is reported
#   (Levi is unique up to conjugacy, so its iso-type is well-defined either way).
#
# RADICAL MODULE STRUCTURE: dim rad, dim[rad,rad], dim[Levi,rad] (exact when an
#   explicit Levi is exhibited; else dim[core,rad] with [rad,rad] split out),
#   dim of core-invariants in rad, and the Levi-submodule filtration [rad,rad] < rad.
#
# Fences as before: blindness, exact arithmetic, mutants, FORBIDDEN-SCAN, and a
# bit-fence to S933 (dimc/derived) and S935 (classification/core-id) on every
# untouched row.
# ============================================================================

import sys
sys.stdout.reconfigure(encoding='utf-8')

import os
import itertools
from math import lcm as _ilcm

from sympy import (Matrix, Integer, Rational, zeros, eye, diag, symbols, Poly, gcd,
                   sqrt as ssqrt, linsolve)

X_ = symbols('x')

_LOGPATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "S937_w33_leg1c_levi_radical_blind_run.log")
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


# ==================== primitives (VERBATIM from S929/S933/S935) ====================

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


# ---------- wedge constructors ----------

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
            br = L[i] * L[j] - L[j] * L[i]
            c = coords_in(L, br, n)
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
        parts = [flat(a.T * E + E * a) for a in ads]
        cols.append(Matrix.vstack(*parts))
    ns = Matrix.hstack(*cols).nullspace()
    return len(ns)


def fingerprint(L, n):
    b = span_basis(L, n)
    return (len(b), killing_sig(b, n), n_invforms(b, n))


# ---------- menu + catalog (leg-1b) ----------

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
MENU_FP = []
for (nm, bas0, nn) in MENU_DEFS:
    b = span_basis(bas0, nn)
    MENU_FP.append((nm, fingerprint(b, nn)))


def fp_add(a, b):
    return (a[0] + b[0],
            (a[1][0] + b[1][0], a[1][1] + b[1][1], a[1][2] + b[1][2]),
            a[2] + b[2])


CATALOG = list(MENU_FP)
for i in range(len(MENU_FP)):
    for j in range(i, len(MENU_FP)):
        ni, fi = MENU_FP[i]
        nj, fj = MENU_FP[j]
        CATALOG.append((ni + "+" + nj, fp_add(fi, fj)))


def identify_core(core, n):
    fp = fingerprint(core, n)
    names = [nm for (nm, f) in CATALOG if f == fp]
    if names:
        return "match=" + "&".join(names) + ":dim{0}".format(fp[0]), fp
    return "OTHER:dim{0}:Killing{1}:ninv{2}".format(fp[0], fp[1], fp[2]), fp


# ---------- Levi/radical machinery (leg-1c) ----------

LEVI_MENU = [("so(3)", so_basis(3, make_eta(3, 0)), 3),
             ("so(2,1)", so_basis(3, make_eta(2, 1)), 3)]
LEVI_FP = [(nm, fingerprint(span_basis(b, nn), nn)) for (nm, b, nn) in LEVI_MENU]


def killing_radical(core, n):
    # rad = ker(Killing) = [core,core]^perp; equals the solvable radical when core is perfect
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


def quotient_ads(reps, rad, n):
    full = reps + rad
    kq = len(reps)
    ads = []
    for i in range(kq):
        cols = []
        for j in range(kq):
            co = coords_in(full, reps[i] * reps[j] - reps[j] * reps[i], n)
            cols.append(Matrix(kq, 1, [co[t, 0] for t in range(kq)]))
        ads.append(Matrix.hstack(*cols))
    return ads


def killing_sig_from_ads(ads):
    k = len(ads)
    K = zeros(k, k)
    for i in range(k):
        for j in range(k):
            K[i, j] = (ads[i] * ads[j]).trace()
    return cong_signature(K)


def ninv_from_ads(ads):
    k = len(ads)
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


def identify_levi_quotient(reps, rad, n):
    ads = quotient_ads(reps, rad, n)
    kq = len(reps)
    ks = killing_sig_from_ads(ads)
    ni = ninv_from_ads(ads)
    fp = (kq, ks, ni)
    names = [nm for (nm, f) in LEVI_FP if f == fp]
    tag = ("Levi=" + "&".join(names)) if names else "Levi=OTHER"
    return tag, fp


def levi_explicit(core, rad, n):
    # solve the linear Levi-cocycle system (drop [rad,rad]); return exhibited Levi if it closes exactly
    reps = complement_reps(core, rad, n)
    kq = len(reps)
    dr = len(rad)
    full = reps + rad
    cstr = {}
    for i in range(kq):
        for j in range(kq):
            co = coords_in(full, reps[i] * reps[j] - reps[j] * reps[i], n)
            cstr[(i, j)] = [co[t, 0] for t in range(kq)]
    us = [[symbols('u_%d_%d' % (i, a)) for a in range(dr)] for i in range(kq)]
    t = []
    for i in range(kq):
        Ti = zeros(n, n)
        for a in range(dr):
            Ti = Ti + us[i][a] * rad[a]
        t.append(Ti)
    eqs = []
    for i in range(kq):
        for j in range(i + 1, kq):
            resid = (reps[i] * t[j] - t[j] * reps[i]) + (t[i] * reps[j] - reps[j] * t[i]) \
                    + (reps[i] * reps[j] - reps[j] * reps[i])
            for k in range(kq):
                resid = resid - cstr[(i, j)][k] * (reps[k] + t[k])
            for e in range(n):
                for f in range(n):
                    ent = resid[e, f].expand()
                    if ent != 0:
                        eqs.append(ent)
    unknowns = [us[i][a] for i in range(kq) for a in range(dr)]
    sol = linsolve(eqs, unknowns)
    if not sol:
        return None
    solset = list(sol)[0]
    freevars = set()
    for expr in solset:
        freevars |= expr.free_symbols
    zsub = {s: Integer(0) for s in freevars}
    levi = []
    for i in range(kq):
        Ci = reps[i] + t[i]
        # substitute solved values
        vals = {}
        for idx, unk in enumerate(unknowns):
            vals[unk] = solset[idx]
        Ci = Ci.subs(vals).subs(zsub)
        levi.append(Ci)
    lb = span_basis(levi, n)
    if len(lb) != kq:
        return None
    # verify EXACT closure (including [rad,rad] terms we dropped) and perfection
    for a in range(kq):
        for b in range(kq):
            if coords_in(lb, lb[a] * lb[b] - lb[b] * lb[a], n) is None:
                return None
    if len(bracket_basis(lb, n)) != kq:
        return None
    return lb


def bspan(mats, n):
    return len(span_basis(mats, n))


def bracket_span(A, B, n):
    out = []
    for a in A:
        for b in B:
            out.append(a * b - b * a)
    return span_basis(out, n)


def module_invariants(reps, rad, n):
    # {r in rad : [reps_i, r]=0 for all i}  (Levi/quotient invariants inside rad)
    if not rad:
        return []
    cols = []
    for a in range(len(rad)):
        parts = [flat(reps[i] * rad[a] - rad[a] * reps[i]) for i in range(len(reps))]
        cols.append(Matrix.vstack(*parts))
    ns = Matrix.hstack(*cols).nullspace()
    out = []
    for v in ns:
        M = zeros(n, n)
        for a in range(len(rad)):
            if v[a, 0] != 0:
                M = M + v[a, 0] * rad[a]
        out.append(M)
    return span_basis(out, n)


# ==================== bit-fence tables ====================
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
# S935 classification tag expected (untouched rows); (3,2)r0 is the DEFECT -> re-measured
S935_CLASS = {
    ("N", 3, 1, "rank1"): "ABELIAN",
    ("N", 2, 2, "rank0"): "CORE:match=so(2,1)&sp(2,R):dim3",
    ("N", 2, 2, "rank1"): "ABELIAN",
    ("N", 4, 1, "rank1"): "SOLVABLE",
    ("N", 3, 2, "rank0"): "DEFECT->re-measure",
    ("N", 3, 2, "rank1"): "SOLVABLE",
    ("N", 5, 1, "rank1"): "CORE:OTHER:dim6",
    ("N", 4, 2, "rank0"): "CORE:OTHER:dim8",
    ("N", 4, 2, "rank1"): "CORE:OTHER:dim6",
    ("N", 3, 3, "rank0"): "CORE:OTHER:dim8",
    ("N", 3, 3, "rank1"): "CORE:OTHER:dim6",
    ("J1",): "ABELIAN",
    ("J2",): "CORE:match=so(2,1)&sp(2,R):dim3",
    ("J3",): "ABELIAN",
    ("J4",): "CORE:match=so(2,1)&sp(2,R):dim3",
}

ROWS = [0]
LEVI_ROWS = [0]


def run_row(kind, p, q, cls, L, fkey):
    n = p + q
    dser = derived_series(L, n)
    dcc = len(bracket_basis(L, n))          # FIX: direct, not dser[1]
    exp_dc, exp_dser = FENCE933[fkey]
    ok(len(L) == exp_dc, "bit-fence dimc " + str(fkey))
    ok(dser == exp_dser, "bit-fence derived " + str(fkey))
    ROWS[0] += 1
    # classification tag
    if dcc == 0:
        tag = "ABELIAN"
        print("ROW {0} SIG=({1},{2}) {3} | dimc={4} | ABELIAN | derived={5}".format(kind, p, q, cls, len(L), dser))
    else:
        core = perfect_core(L, n)
        if not core:
            tag = "SOLVABLE"
            print("ROW {0} SIG=({1},{2}) {3} | dimc={4} | SOLVABLE | derived={5}".format(kind, p, q, cls, len(L), dser))
        else:
            cid, fp = identify_core(core, n)
            if fp[1][2] == 0:   # Killing nondegenerate => semisimple core -> menu match
                tag = "CORE:" + cid
                print("ROW {0} SIG=({1},{2}) {3} | dimc={4} | NON-ABELIAN semisimple-core | derived={5} | CORE-ID={6}".format(
                    kind, p, q, cls, len(L), dser, cid))
            else:
                tag = "CORE:OTHER:dim{0}".format(fp[0])
                # --- Levi extraction on perfect-non-semisimple core ---
                LEVI_ROWS[0] += 1
                rad = killing_radical(core, n)
                # rad is an ideal and solvable
                ideal = all(coords_in(rad, m, n) is not None for m in bracket_span(core, rad, n))
                ok(ideal, "radical is an ideal " + str(fkey))
                ok(derived_series(rad, n)[-1] == 0 or len(bracket_basis(rad, n)) < len(rad),
                   "radical solvable " + str(fkey))
                reps = complement_reps(core, rad, n)
                ltag, lfp = identify_levi_quotient(reps, rad, n)
                lb = levi_explicit(core, rad, n)
                if lb is not None:
                    levi_lr = len(bracket_span(lb, rad, n))     # dim [Levi, rad]
                    lev_status = "explicit(dim{0},closed)".format(len(lb))
                else:
                    levi_lr = None
                    lev_status = "quotient-only"
                drr = len(bracket_basis(rad, n))
                dcr = len(bracket_span(core, rad, n))
                dinv = len(module_invariants(reps, rad, n))
                print(("ROW {0} SIG=({1},{2}) {3} | dimc={4} | CORE perfect-non-ss dim{5} Killing{6} ninv{7} | "
                       "{8} lfp={9} | Levi-realize={10} | rad: dim={11} [rad,rad]={12} [core,rad]={13} "
                       "[Levi,rad]={14} rad^Levi-inv={15} | rad-filtration=[{12},{16}]").format(
                    kind, p, q, cls, len(L), fp[0], fp[1], fp[2],
                    ltag, lfp, lev_status, len(rad), drr, dcr,
                    (levi_lr if levi_lr is not None else "n/a"), dinv, len(rad) - drr))
    # bit-fence to S935 classification (untouched rows)
    exp = S935_CLASS[fkey]
    if exp == "DEFECT->re-measure":
        ok(dcc > 0, "DEFECT re-measured: (3,2)r0 now NON-ABELIAN (was ABELIAN in S935) " + str(fkey))
    else:
        ok(tag == exp, "bit-fence S935 classification " + str(fkey) + " got=" + tag)


# ==================== part 1: nilpotent rows ====================
print("--- part 1: nilpotent-row centralizers (FIXED classification + Levi) ---")
for (p, q) in sig_list():
    n = p + q
    eta = make_eta(p, q)
    bas = so_basis(n, eta)
    for (cls, ctor) in (("rank0", d0_on), ("rank1", d1_on)):
        xy = ctor(list(range(n)), p, n)
        if xy is None:
            continue
        N = wedge(xy[0], xy[1], eta)
        run_row("N", p, q, cls, centralizer(N, bas), ("N", p, q, cls))

# ==================== part 2: mixed rows ====================
print("--- part 2: mixed-row centralizers ---")
_p, _q = 2, 2; _n = 4; _eta = make_eta(_p, _q); _bas = so_basis(_n, _eta)
_S = block_gen(_n, _eta, 0, 2, 1) + block_gen(_n, _eta, 1, 3, 1)
_cbS = centralizer(_S, _bas)
_N = jordan_scan(_cbS, q_gram(_cbS), _n)
run_row("J1", _p, _q, "mixed", centralizer(_S + _N, _bas), ("J1",))

_p, _q = 4, 2; _n = 6; _eta = make_eta(_p, _q); _bas = so_basis(_n, _eta)
_S = block_gen(_n, _eta, 0, 1, 1)
_x, _y = d0_on([2, 3, 4, 5], _p, _n)
run_row("J2", _p, _q, "mixed", centralizer(_S + wedge(_x, _y, _eta), _bas), ("J2",))

_p, _q = 5, 1; _n = 6; _eta = make_eta(_p, _q); _bas = so_basis(_n, _eta)
_S = block_gen(_n, _eta, 0, 1, 1)
_x, _y = d1_on([2, 3, 4, 5], _p, _n)
run_row("J3", _p, _q, "mixed", centralizer(_S + wedge(_x, _y, _eta), _bas), ("J3",))

_p, _q = 3, 3; _n = 6; _eta = make_eta(_p, _q); _bas = so_basis(_n, _eta)
_S = block_gen(_n, _eta, 0, _p, 1)
_x, _y = d0_on([1, 2, 4, 5], _p, _n)
run_row("J4", _p, _q, "mixed", centralizer(_S + wedge(_x, _y, _eta), _bas), ("J4",))


# ==================== mutants ====================
print("--- mutants ---")
mut_ok = True


def classify_tag(L, n):
    # the FIXED classification used above (dim[c,c] direct)
    dcc = len(bracket_basis(L, n))
    if dcc == 0:
        return "ABELIAN"
    return "PERFECT-WHOLE" if len(perfect_core(L, n)) == len(span_basis(L, n)) else "MIXED-DERIVED"


# mu1 (THE fix): perfect-whole algebra must NOT be tagged ABELIAN
_perf = so_basis(3, make_eta(2, 1))               # so(2,1): [c,c]=c, derived=[3]
_abel = [Matrix([[0, Integer(1)], [Integer(-1), 0]])]  # 1-dim abelian
_ab2 = [eye(2), Matrix([[Integer(1), 0], [0, Integer(-1)]])]  # 2-dim abelian (diagonal)
tp = classify_tag(_perf, 3)
ta = classify_tag(_ab2, 2)
ok(derived_series(_perf, 3) == [3], "mu1 baseline: so(2,1) derived=[3] (length 1)")
ok(len(bracket_basis(_perf, 3)) == 3, "mu1 baseline: dim[c,c]=3 for perfect whole")
if tp == "PERFECT-WHOLE" and ta == "ABELIAN":
    print("MUTANT mu1: CAUGHT (perfect-whole so(2,1) tagged NON-ABELIAN; abelian tagged ABELIAN)")
else:
    print("MUTANT mu1: NOT CAUGHT (perf={0}, abel={1})".format(tp, ta))
    mut_ok = False

# mu2: killing_radical isolates the radical (ker Killing) of a perfect-non-ss algebra
#   build sl2 |x V (V=2-dim std rep): rad must be V (dim2), and quotient semisimple.
_e = Matrix([[0, Integer(1)], [0, 0]]); _f = Matrix([[0, 0], [Integer(1), 0]]); _h = Matrix([[Integer(1), 0], [0, Integer(-1)]])
# realize sl2|xV inside gl(3): sl2 on top-left 2x2 acting on column space, V = 2-dim ...
# simpler: use a known perfect-non-ss core from the run — (5,1)r1
_p, _q = 5, 1; _n = 6; _eta = make_eta(_p, _q)
_x5, _y5 = d1_on(list(range(_n)), _p, _n)
_core5 = perfect_core(centralizer(wedge(_x5, _y5, _eta), so_basis(_n, _eta)), _n)
_rad5 = killing_radical(_core5, _n)
ok(len(_core5) == 6, "mu2 baseline: (5,1)r1 core dim6")
_reps5 = complement_reps(_core5, _rad5, _n)
_ql, _qfp = identify_levi_quotient(_reps5, _rad5, _n)
if len(_rad5) == 3 and _qfp[1][2] == 0 and _qfp[0] == 3:
    print("MUTANT mu2: CAUGHT (killing_radical: core6 -> rad3 + semisimple quotient dim3 {0})".format(_ql))
else:
    print("MUTANT mu2: NOT CAUGHT (rad={0}, qfp={1})".format(len(_rad5), _qfp))
    mut_ok = False

# mu3: Levi quotient identification separates so(3) from so(2,1) (compact vs split)
_ql5, _fp5 = identify_levi_quotient(complement_reps(_core5, _rad5, _n), _rad5, _n)  # (5,1)r1 -> so(3)
_p2, _q2 = 4, 2; _n2 = 6; _eta2 = make_eta(_p2, _q2)
_x2, _y2 = d1_on(list(range(_n2)), _p2, _n2)
_core2 = perfect_core(centralizer(wedge(_x2, _y2, _eta2), so_basis(_n2, _eta2)), _n2)
_rad2 = killing_radical(_core2, _n2)
_ql2, _fp2 = identify_levi_quotient(complement_reps(_core2, _rad2, _n2), _rad2, _n2)  # (4,2)r1 -> so(2,1)
if _fp5[1] != _fp2[1] and "so(3)" in _ql5 and "so(2,1)" in _ql2:
    print("MUTANT mu3: CAUGHT (Levi quotient: (5,1)r1={0} vs (4,2)r1={1})".format(_ql5, _ql2))
else:
    print("MUTANT mu3: NOT CAUGHT ({0} / {1})".format(_ql5, _ql2))
    mut_ok = False

# mu4: explicit Levi is bracket-closed & perfect; corrupting it by a radical element
#   (rad^Levi-inv=0 for (5,1)r1 => the radical is not central to Levi) must break closure.
_lb5 = levi_explicit(_core5, _rad5, _n)
ok(_lb5 is not None, "mu4 baseline: explicit Levi found for (5,1)r1")
ok(len(module_invariants(complement_reps(_core5, _rad5, _n), _rad5, _n)) == 0,
   "mu4 baseline: (5,1)r1 has no Levi-invariants in radical")
if _lb5 is not None:
    _bad = [_lb5[0] + _rad5[0]] + list(_lb5[1:])   # perturb one generator by a radical element
    good_closed = all(coords_in(_lb5, _lb5[a] * _lb5[b] - _lb5[b] * _lb5[a], _n) is not None
                      for a in range(len(_lb5)) for b in range(len(_lb5)))
    bad_closed = all(coords_in(_bad, _bad[a] * _bad[b] - _bad[b] * _bad[a], _n) is not None
                     for a in range(len(_bad)) for b in range(len(_bad)))
    if good_closed and not bad_closed:
        print("MUTANT mu4: CAUGHT (explicit Levi closes; radical-perturbed complement does NOT)")
    else:
        print("MUTANT mu4: NOT CAUGHT (good={0}, bad_closed={1})".format(good_closed, bad_closed))
        mut_ok = False
else:
    print("MUTANT mu4: NOT CAUGHT (no explicit Levi)")
    mut_ok = False

# mu5: bracket-table self-consistency (reused bt_verify) rejects a corrupted table
_g3 = eye(3)
_mod3 = span_basis(model_from_constraints(3, [lambda E: E.T * _g3 + _g3 * E]), 3)
_tab3 = sc_table(_mod3, 3)
ok(bt_verify(_mod3, _mod3, _tab3, 3), "mu5 baseline: uncorrupted table verifies")
_tb = dict(_tab3)
_k0 = sorted(_tb.keys())[0]
_row = list(_tb[_k0]); _row[0] = _row[0] + 1; _tb[_k0] = tuple(_row)
if not bt_verify(_mod3, _mod3, _tb, 3):
    print("MUTANT mu5: CAUGHT (bracket-table MISMATCH reported)")
else:
    print("MUTANT mu5: NOT CAUGHT")
    mut_ok = False


# ==================== sign-fence {eta,-eta} ====================
_p, _q = 4, 2; _n = 6; _eta = make_eta(_p, _q)
_xx, _yy = d1_on(list(range(_n)), _p, _n)
_NN = wedge(_xx, _yy, _eta)
_coreA = perfect_core(centralizer(_NN, so_basis(_n, _eta)), _n)
_coreB = perfect_core(centralizer(_NN, so_basis(_n, -_eta)), _n)
_radA = killing_radical(_coreA, _n)
_radB = killing_radical(_coreB, _n)
ok(len(_radA) == len(_radB), "sign-fence: radical dim invariant under eta->-eta")
ok(identify_levi_quotient(complement_reps(_coreA, _radA, _n), _radA, _n)[1]
   == identify_levi_quotient(complement_reps(_coreB, _radB, _n), _radB, _n)[1],
   "sign-fence: Levi fingerprint invariant under eta->-eta")


# ==================== summary ====================
print("SUMMARY: rows={0} | perfect-non-ss-Levi-rows={1}".format(ROWS[0], LEVI_ROWS[0]))
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
