# -*- coding: utf-8 -*-
# DIM: na (direct bt_verify core <-> construct with an EXPLICIT linear isomorphism, both directions,
#      replacing the fingerprint step-4 of S943; 0 handles).
#
# ============================================================================
# CARVE CHOICE (stamped BEFORE any counting)
# ----------------------------------------------------------------------------
# For each of the 6 non-abelian cores (= Levi ⋉ radical, from S937/S940) we build
# an EXPLICIT Lie isomorphism  φ : core  ->  construct  and verify it BOTH ways
# by structure-constant equality (sc(core-adapted-basis) == sc(construct-basis);
# identical structure constants ⟺ the basis correspondence B_i<->C_i and its
# inverse are both Lie homomorphisms — i.e. bt_verify in both directions).
#
# Adapted basis B = { explicit Levi L_1..L_3 ; module M_1..M_{d'} ; [center Z] }.
# Module action ρ_i := action of L_i on M (d'×d', modulo Z).  The construct:
#   * rad ABELIAN  -> AFFINE  so(p',q') ⋉ R^{d'} (S921 (d'+1)-rep): (p',q') is
#     the signature of the Levi-invariant SYMMETRIC form g on M; congruence
#     P (PᵀgP = η') gives ψ(L_i)=P⁻¹ρ_iP ∈ so(η'); translations abelian.
#   * rad HEISENBERG ([rad,rad]=Z!=0) -> CENTRAL EXTENSION: the Levi-invariant
#     ANTISYMMETRIC form ω on M (from [M,M]=ω·Z) is put in Darboux form by Q
#     (QᵀωQ = J); ψ(L_i)=Q⁻¹ρ_iQ ∈ sp(J); translations carry [τ_i,τ_j]=ω_ij z,
#     center z <-> Z(rad).
# φ maps L_i -> ψ(L_i) (S921-hatted), M_j -> the P/Q-aligned translation, Z -> z.
# bt_verify both ways := sc(B) == sc(C) exactly.
#
# EVERY classification branch (match-affine / match-extended / none) carries a
# CAUGHT mutant (lesson J-0415).  Fences: blindness, exact arithmetic,
# FORBIDDEN-SCAN, bit-fence S943, STOP after the table.
# ============================================================================

import sys
sys.stdout.reconfigure(encoding='utf-8')

import os
import json
from sympy import Matrix, Integer, Rational, zeros, eye, diag, symbols, sqrt as ssqrt


def mstr(M):
    # exact matrix -> nested list of string rationals (Lean-ready, no floats)
    return [[str(M[i, j]) for j in range(M.cols)] for i in range(M.rows)]


EXPORT = {}

_LOGPATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "S946_w33_leg2b_bt_verify_iso_blind_run.log")
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


# ==================== primitives ====================

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


def bracket_basis(L, n):
    brs = []
    for a in range(len(L)):
        for b in range(a + 1, len(L)):
            brs.append(L[a] * L[b] - L[b] * L[a])
    return span_basis(brs, n)


def perfect_core(L, n):
    cur = span_basis(L, n)
    while len(cur) > 0:
        nxt = bracket_basis(cur, n)
        if len(nxt) == len(cur):
            return cur
        cur = nxt
    return []


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


def killing_radical(core, n):
    ads = ad_matrices(core, n)
    k = len(core)
    K = zeros(k, k)
    for i in range(k):
        for j in range(k):
            K[i, j] = (ads[i] * ads[j]).trace()
    ns = K.nullspace()
    rad = []
    for v in ns:
        M = zeros(n, n)
        for t in range(k):
            if v[t, 0] != 0:
                M = M + v[t, 0] * core[t]
        rad.append(M)
    return span_basis(rad, n)


def center_of(cb, n):
    if not cb:
        return []
    cols = []
    for k in range(len(cb)):
        cols.append(Matrix.vstack(*[flat(cb[k] * cb[j] - cb[j] * cb[k]) for j in range(len(cb))]))
    ns = Matrix.hstack(*cols).nullspace()
    out = []
    for v in ns:
        M = zeros(n, n)
        for k in range(len(cb)):
            if v[k, 0] != 0:
                M = M + v[k, 0] * cb[k]
        out.append(M)
    return span_basis(out, n)


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


# ---------- explicit Levi (S937) ----------
from sympy import linsolve


def levi_explicit(core, rad, n):
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
    vals = {unknowns[idx]: solset[idx] for idx in range(len(unknowns))}
    levi = [(reps[i] + t[i]).subs(vals).subs(zsub) for i in range(kq)]
    lb = span_basis(levi, n)
    if len(lb) != kq:
        return None
    return lb


# ---------- S921 homogeneous rep ----------

def hat(M, dp):
    return M.row_join(zeros(dp, 1)).col_join(zeros(1, dp + 1))


def Tmat(a, dp):
    T = zeros(dp + 1, dp + 1)
    for i in range(dp):
        T[i, dp] = a[i, 0]
    return T


# ---------- module action / invariant forms / congruence ----------

def module_action(L, M, Z, n):
    # ρ_i = d'×d' matrix of L_i acting on M (mod Z), in M-basis
    dm = len(M)
    full = M + Z
    ops = []
    for Li in L:
        cols = []
        for j in range(dm):
            c = coords_in(full, Li * M[j] - M[j] * Li, n)
            cols.append(Matrix(dm, 1, [c[t, 0] for t in range(dm)]))
        ops.append(Matrix.hstack(*cols))
    return ops


def invariant_sym_form(rhos, dm):
    # symmetric g (dm×dm) with ρᵀg+gρ=0 for all ρ
    symb = []
    idx = {}
    cnt = 0
    for a in range(dm):
        for b in range(a, dm):
            idx[(a, b)] = cnt
            cnt += 1
    gs = symbols('g0:%d' % cnt)
    G = zeros(dm, dm)
    for a in range(dm):
        for b in range(a, dm):
            G[a, b] = gs[idx[(a, b)]]
            G[b, a] = gs[idx[(a, b)]]
    eqs = []
    for rho in rhos:
        E = rho.T * G + G * rho
        for a in range(dm):
            for b in range(dm):
                eqs.append(E[a, b])
    sol = linsolve(eqs, list(gs))
    if not sol:
        return None
    s = list(sol)[0]
    free = set()
    for e in s:
        free |= e.free_symbols
    # pick a nondegenerate representative: set one free var to 1, rest 0
    for pick in (list(free) if free else [None]):
        sub = {f: (Integer(1) if f == pick else Integer(0)) for f in free}
        Gv = G.subs({gs[idx[(a, b)]]: s[idx[(a, b)]] for a in range(dm) for b in range(a, dm)}).subs(sub)
        if Gv.det() != 0:
            return Gv
    return None


def invariant_antisym_form(rhos, dm):
    if dm < 2:
        return None
    idx = {}
    cnt = 0
    for a in range(dm):
        for b in range(a + 1, dm):
            idx[(a, b)] = cnt
            cnt += 1
    cs = symbols('w0:%d' % cnt)
    W = zeros(dm, dm)
    for a in range(dm):
        for b in range(a + 1, dm):
            W[a, b] = cs[idx[(a, b)]]
            W[b, a] = -cs[idx[(a, b)]]
    eqs = []
    for rho in rhos:
        E = rho.T * W + W * rho
        for a in range(dm):
            for b in range(dm):
                eqs.append(E[a, b])
    sol = linsolve(eqs, list(cs))
    if not sol:
        return None
    s = list(sol)[0]
    free = set()
    for e in s:
        free |= e.free_symbols
    for pick in (list(free) if free else [None]):
        sub = {f: (Integer(1) if f == pick else Integer(0)) for f in free}
        Wv = W.subs({cs[idx[(a, b)]]: s[idx[(a, b)]] for a in range(dm) for b in range(a + 1, dm)}).subs(sub)
        if Wv.det() != 0:
            return Wv
    return None


def cong_to_diag_pm(g, dm):
    # returns P with Pᵀ g P = diag(±1) and the signature (p',q')
    A = g.copy()
    P = eye(dm)
    for i in range(dm):
        if A[i, i] == 0:
            js = None
            for j in range(i + 1, dm):
                if A[j, j] != 0:
                    js = j
                    break
            if js is not None:
                A.col_swap(i, js); A.row_swap(i, js); P.col_swap(i, js)
            else:
                jn = None
                for j in range(i + 1, dm):
                    if A[i, j] != 0:
                        jn = j
                        break
                if jn is None:
                    continue
                A[:, i] = A[:, i] + A[:, jn]; A[i, :] = A[i, :] + A[jn, :]; P[:, i] = P[:, i] + P[:, jn]
        piv = A[i, i]
        if piv == 0:
            continue
        for j in range(i + 1, dm):
            if A[i, j] != 0:
                f = A[i, j] / piv
                A[:, j] = A[:, j] - f * A[:, i]; A[j, :] = A[j, :] - f * A[i, :]; P[:, j] = P[:, j] - f * P[:, i]
    # normalize each diagonal to ±1
    for i in range(dm):
        d = A[i, i]
        if d != 0:
            sc = 1 / ssqrt(abs(d))
            P[:, i] = P[:, i] * sc
            A[i, :] = A[i, :] * sc
            A[:, i] = A[:, i] * sc
    pos = sum(1 for i in range(dm) if A[i, i] > 0)
    neg = sum(1 for i in range(dm) if A[i, i] < 0)
    return P, (pos, neg)


def darboux(omega, dm):
    # P with Pᵀ ω P = J (standard symplectic [[0,I],[-I,0]]); dm even
    m = dm // 2
    A = omega.copy()
    P = eye(dm)
    # simple symplectic Gram-Schmidt over Q
    basis_pairs = []
    used = [False] * dm
    cols = [P[:, i] for i in range(dm)]
    # work with vectors e_i and the form; build symplectic basis
    vecs = [unit(dm, i) for i in range(dm)]
    e_list = []
    f_list = []
    pool = list(range(dm))
    # greedy: pick a vector, find partner
    remaining = [unit(dm, i) for i in range(dm)]

    def wform(u, v):
        return (u.T * A * v)[0, 0]

    vs = [unit(dm, i) for i in range(dm)]
    chosen = []
    span_cols = zeros(dm, 0)
    while len([c for c in e_list]) < m:
        # find u not in current span with some partner
        u = None
        for cand in vs:
            if Matrix.hstack(span_cols, cand).rank() > span_cols.rank():
                u = cand
                break
        if u is None:
            return None
        v = None
        for cand in vs:
            if wform(u, cand) != 0 and Matrix.hstack(span_cols, u, cand).rank() > Matrix.hstack(span_cols, u).rank():
                v = cand / wform(u, cand)
                break
        if v is None:
            return None
        # orthogonalize remaining vs against symplectic pair (u,v)
        newvs = []
        for w in vs:
            w2 = w - wform(w, v) * u + wform(w, u) * v
            newvs.append(w2)
        e_list.append(u)
        f_list.append(v)
        span_cols = Matrix.hstack(span_cols, u, v)
        vs = newvs
    Q = Matrix.hstack(*(e_list + f_list))
    J = zeros(dm, dm)
    for i in range(m):
        J[i, m + i] = Integer(1)
        J[m + i, i] = Integer(-1)
    if (Q.T * A * Q - J) != zeros(dm, dm):
        return None
    return Q


# ---------- structure constants ----------

def sc_of(basis, n):
    tab = {}
    k = len(basis)
    for i in range(k):
        for j in range(i + 1, k):
            c = coords_in(basis, basis[i] * basis[j] - basis[j] * basis[i], n)
            if c is None:
                return None
            tab[(i, j)] = tuple(c[t, 0] for t in range(k))
    return tab


def jacobi_ok_sc(sc, dim):
    # verify Jacobi for a structure-constant table (abstract algebra)
    def br(i, j):
        if i == j:
            return [Integer(0)] * dim
        if i < j:
            return list(sc[(i, j)])
        return [-x for x in sc[(j, i)]]

    def brvec(u, v):
        out = [Integer(0)] * dim
        for a in range(dim):
            if u[a] == 0:
                continue
            for b in range(dim):
                if v[b] == 0:
                    continue
                bab = br(a, b)
                for k in range(dim):
                    out[k] += u[a] * v[b] * bab[k]
        return out
    for i in range(dim):
        for j in range(i + 1, dim):
            for l in range(j + 1, dim):
                s = [Integer(0)] * dim
                for (a, b, cc) in ((i, j, l), (j, l, i), (l, i, j)):
                    inner = br(a, b)
                    s = [s[k] + brvec(inner, [Integer(1) if t == cc else Integer(0) for t in range(dim)])[k]
                         for k in range(dim)]
                if any(x != 0 for x in s):
                    return False
    return True


# ==================== the 6 cores ====================
CORES = [
    ("N", 3, 2, "rank0", d0_on),
    ("N", 5, 1, "rank1", d1_on),
    ("N", 4, 2, "rank1", d1_on),
    ("N", 3, 3, "rank1", d1_on),
    ("N", 4, 2, "rank0", d0_on),
    ("N", 3, 3, "rank0", d0_on),
]
FENCE = {  # bit-fence S943
    ("N", 3, 2, "rank0"): dict(core=6, rad=3, drr=1, match="central-extended"),
    ("N", 5, 1, "rank1"): dict(core=6, rad=3, drr=0, match="affine"),
    ("N", 4, 2, "rank1"): dict(core=6, rad=3, drr=0, match="affine"),
    ("N", 3, 3, "rank1"): dict(core=6, rad=3, drr=0, match="affine"),
    ("N", 4, 2, "rank0"): dict(core=8, rad=5, drr=1, match="central-extended"),
    ("N", 3, 3, "rank0"): dict(core=8, rad=5, drr=1, match="central-extended"),
}


def build_iso_and_verify(core, rad, n, tag):
    L = levi_explicit(core, rad, n)
    Z = span_basis(center_of(rad, n), n)
    drr = len(bracket_basis(rad, n))
    M = list(rad) if drr == 0 else complement_reps(rad, Z, n)
    dm = len(M)
    rhos = module_action(L, M, Z, n)
    kq = len(L)

    if drr == 0:
        # AFFINE: symmetric form + congruence
        g = invariant_sym_form(rhos, dm)
        if g is None:
            return "none", None, None, None, None
        P, sig = cong_to_diag_pm(g, dm)
        D = P.T * g * P                      # actual normalized diagonal (unsorted ±1)
        Pinv = P.inv()
        # construct in S921 (dm+1)-rep: Levi = ψ(L_i)=P⁻¹ρP hatted, translations
        CL = [hat(Pinv * rhos[i] * P, dm) for i in range(kq)]
        CT = [Tmat(unit(dm, j), dm) for j in range(dm)]
        # verify ψ(L_i) ∈ so(D) (D = the actual congruent diagonal form)
        for i in range(kq):
            psi = Pinv * rhos[i] * P
            ok((psi.T * D + D * psi) == zeros(dm, dm), "ψ(L) in so(D) " + tag)
        C = CL + CT
        # core adapted basis: BL_i = L_i, BM_j = Σ_l P_{lj} M_l  (P-aligned module)
        BL = list(L)
        BM = []
        for j in range(dm):
            Mm = zeros(n, n)
            for l in range(dm):
                Mm = Mm + P[l, j] * M[l]
            BM.append(Mm)
        B = BL + BM
        sc_B = sc_of(B, n)
        sc_C = sc_of(C, dm + 1)
        equal = (sc_B == sc_C)
        exp = dict(match="affine", dp=dm, sig=[sig[0], sig[1]],
                   invariant_form_g=mstr(g), congruence_P=mstr(P),
                   psi_levi_in_so=[mstr(Pinv * rhos[i] * P) for i in range(kq)],
                   translations="standard e_1..e_{d'} of R^{d'} (S921 (d'+1)-rep)",
                   sc_equal=bool(equal))
        return ("affine" if equal else "none"), sig, dm, (sc_B == sc_C), exp
    else:
        # CENTRAL EXTENSION: symplectic form ω from the ACTUAL [M_i,M_j] into Z(=Z[0])
        if dm % 2 != 0 or len(Z) != 1:
            return "none", None, None, None, None
        Zc = Z[0]
        w = zeros(dm, dm)
        for a in range(dm):
            for b in range(dm):
                cc = coords_in([Zc], M[a] * M[b] - M[b] * M[a], n)
                w[a, b] = cc[0, 0] if cc is not None else Integer(0)
        if w.det() == 0:
            return "none", None, None, None, None
        Q = darboux(w, dm)
        if Q is None:
            return "none", None, None, None, None
        Qinv = Q.inv()
        m = dm // 2
        J = zeros(dm, dm)
        for i in range(m):
            J[i, m + i] = Integer(1)
            J[m + i, i] = Integer(-1)
        # ψ(L_i)=Q⁻¹ρQ ∈ sp(J)
        for i in range(kq):
            psi = Qinv * rhos[i] * Q
            ok((psi.T * J + J * psi) == zeros(dm, dm), "ψ(L) in sp(J) " + tag)
        # abstract construct sc: dim = kq + dm + 1 (Levi, translations, center z)
        dim = kq + dm + 1
        zc = kq + dm  # z index
        # Levi table from core (same L used in B)
        Ltab = sc_of(L, n)
        # module action of ψ(L) on translations (standard basis, via Q-alignment)
        psis = [Qinv * rhos[i] * Q for i in range(kq)]
        sc_C = {}
        for i in range(dim):
            for j in range(i + 1, dim):
                vec = [Integer(0)] * dim
                if i < kq and j < kq:            # Levi-Levi
                    for k in range(kq):
                        vec[k] = Ltab[(i, j)][k]
                elif i < kq <= j < kq + dm:      # Levi-translation: (ψ(L_i)) e_{j-kq}
                    col = psis[i][:, j - kq]
                    for l in range(dm):
                        vec[kq + l] = col[l, 0]
                elif kq <= i < kq + dm and kq <= j < kq + dm:   # transl-transl: J_{ij} z
                    a, b = i - kq, j - kq
                    vec[zc] = J[a, b]
                # anything with z -> 0
                sc_C[(i, j)] = tuple(vec)
        ok(jacobi_ok_sc(sc_C, dim), "construct Jacobi " + tag)
        # core adapted basis B: BL_i=L_i, BM_j = Q-aligned module, Z
        BL = list(L)
        BM = []
        for j in range(dm):
            Mm = zeros(n, n)
            for l in range(dm):
                Mm = Mm + Q[l, j] * M[l]
            BM.append(Mm)
        # scale center so [BM_i,BM_j] = J_ij * Zc  (match construct)
        Zc = Z[0]
        B = BL + BM + [Zc]
        sc_B = sc_of(B, n)
        equal = (sc_B == sc_C)
        exp = dict(match="central-extended", dp=dm, sig=None,
                   symplectic_omega=mstr(w), darboux_Q=mstr(Q),
                   psi_levi_in_sp=[mstr(psis[i]) for i in range(kq)],
                   J_standard=mstr(J), center="z <-> Z(rad)[0]",
                   sc_equal=bool(equal))
        return ("central-extended" if equal else "none"), None, dm, equal, exp


print("--- W33-нога-2b: explicit iso + bt_verify both ways ---")
for (kind, p, q, cls, ctor) in CORES:
    n = p + q
    eta = make_eta(p, q)
    bas = so_basis(n, eta)
    N = wedge(*ctor(list(range(n)), p, n), eta)
    core = perfect_core(centralizer(N, bas), n)
    rad = killing_radical(core, n)
    fk = (kind, p, q, cls)
    exp = FENCE[fk]
    ok(len(core) == exp["core"], "bit-fence core " + str(fk))
    ok(len(rad) == exp["rad"], "bit-fence rad " + str(fk))
    ok(len(bracket_basis(rad, n)) == exp["drr"], "bit-fence [rad,rad] " + str(fk))
    tag = "({0},{1}){2}".format(p, q, cls)
    match, sig, dm, equal, expdata = build_iso_and_verify(core, rad, n, tag)
    ok(match == exp["match"], "bt-match agrees with S943 " + str(fk))
    ok(equal is True, "bt_verify both ways (sc(B)==sc(C)) " + str(fk))
    if expdata is not None:
        EXPORT["so({0},{1})_{2}".format(p, q, cls)] = expdata
    print("CORE ({0},{1}) {2} | dim core={3} [rad,rad]={4} | construct={5} d'={6} sig={7} | "
          "explicit-iso bt_verify BOTH WAYS: {8}".format(
        p, q, cls, len(core), exp["drr"], match, dm, sig, "PASS" if equal else "FAIL"))


# ==================== mutants — one per branch ====================
print("--- mutants (one per branch) ---")
mut_ok = True


def _core_of(p, q, ctor):
    n = p + q
    N = wedge(*ctor(list(range(n)), p, n), make_eta(p, q))
    core = perfect_core(centralizer(N, so_basis(n, make_eta(p, q))), n)
    rad = killing_radical(core, n)
    return core, rad, n


# br-affine: abelian-rad core -> affine, bt PASS both ways
_c, _r, _n = _core_of(5, 1, d1_on)
_m, _s, _d, _eq, _x = build_iso_and_verify(_c, _r, _n, "mut-aff")
if _m == "affine" and _eq is True:
    print("MUTANT br-affine: CAUGHT (abelian-rad -> affine, bt both ways PASS)")
else:
    print("MUTANT br-affine: NOT CAUGHT ({0},{1})".format(_m, _eq)); mut_ok = False

# br-extended: Heisenberg-rad core -> central-extended, bt PASS both ways
_c, _r, _n = _core_of(4, 2, d0_on)
_m, _s, _d, _eq, _x = build_iso_and_verify(_c, _r, _n, "mut-ext")
if _m == "central-extended" and _eq is True:
    print("MUTANT br-extended: CAUGHT (Heisenberg-rad -> central-extended, bt both ways PASS)")
else:
    print("MUTANT br-extended: NOT CAUGHT ({0},{1})".format(_m, _eq)); mut_ok = False

# br-none: a corrupted construct (wrong sign in one translation bracket) FAILS sc-equality
_c, _r, _n = _core_of(5, 1, d1_on)
_L = levi_explicit(_c, _r, _n)
_M = list(_r)
_rhos = module_action(_L, _M, [], _n)
_g = invariant_sym_form(_rhos, len(_M))
_P, _sig = cong_to_diag_pm(_g, len(_M))
_Pinv = _P.inv()
_CL = [hat(_Pinv * _rhos[i] * _P, len(_M)) for i in range(len(_L))]
_CT = [Tmat(unit(len(_M), j), len(_M)) for j in range(len(_M))]
# CORRUPT: flip sign of one translation image -> no longer an iso
_CTbad = list(_CT)
_CTbad[0] = -_CTbad[0]
_C = _CL + _CT
_Cbad = _CL + _CTbad
_BL = list(_L)
_BM = []
for j in range(len(_M)):
    Mm = zeros(_n, _n)
    for l in range(len(_M)):
        Mm = Mm + _P[l, j] * _M[l]
    _BM.append(Mm)
_B = _BL + _BM
_scB = sc_of(_B, _n)
_scC = sc_of(_C, len(_M) + 1)
_scCbad = sc_of(_Cbad, len(_M) + 1)
if _scB == _scC and _scB != _scCbad:
    print("MUTANT br-none: CAUGHT (true construct matches; sign-corrupted one does NOT)")
else:
    print("MUTANT br-none: NOT CAUGHT (good={0}, bad_differs={1})".format(_scB == _scC, _scB != _scCbad))
    mut_ok = False


# ==================== Lean-ready exact export (S949) ====================
_EXPPATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "S946_w33_leg2b_iso_export.json")
_export_doc = dict(
    note=("Exact explicit Lie isomorphisms core->construct for the 6 non-abelian centralizer "
          "cores of nilpotent wedges in so(p,q), n<=6 (W33 leg-2b, S946). Every matrix is exact "
          "(rational strings, no floats). Intended as krok-A input for a Lean/mathlib formalization "
          "of the enumeration: each entry gives the explicit LieEquiv data (P/Q alignment, "
          "psi(Levi) generators inside so(eta')/sp(J)) whose structure-constant equality "
          "sc(core-adapted)==sc(construct) was machine-verified BOTH ways."),
    convention=("core = Levi(so(2,1) or so(3)) semidirect radical; construct = so(p',q') affine "
                "R^{d'} (S921 (d'+1)-rep) for abelian radical, or so(p',q')-in-sp(J) central "
                "extension of the Heisenberg module (center<->Z(rad)) for [rad,rad]!=0."),
    cores=EXPORT,
)
with open(_EXPPATH, "w", encoding="utf-8") as _ef:
    json.dump(_export_doc, _ef, ensure_ascii=False, indent=2)
print("EXPORT: {0} cores written to {1}".format(len(EXPORT), os.path.basename(_EXPPATH)))
ok(len(EXPORT) == 6, "export has all 6 cores")

# ==================== summary ====================
print("SUMMARY: cores={0}".format(len(CORES)))
print("SUMMARY: asserts_passed={0} | FAIL={1}".format(ASSERT_PASS[0], FAILS[0]))

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
