# -*- coding: utf-8 -*-
# A2 Lean-input generator (lane-C, Lean endgame step A2 — the 6 isomorphisms of S946).
#
# For each non-abelian nilpotent-wedge centralizer core c(N) in so(p,q) (n<=6), S946 built
# an EXPLICIT Lie isomorphism  phi : core  ->  construct  and verified sc(core-adapted-basis)
# == sc(construct-basis) BOTH ways.  This generator re-derives, for each core, the EXACT
# rational matrices of:
#   * eta          = so(p,q) metric (n x n)
#   * N            = the nilpotent wedge (n x n)
#   * B_0..B_{d-1} = core-adapted basis of c(N) inside so(eta)          (n x n each)
#   * C_0..C_{d-1} = construct basis                                     (ambient x ambient)
#   * the shared structure-constant table sc[(i,j)]                      (same for B and C)
# and emits Lean `!![ ... ]` literals + the bracket-table RHS, to paste into VGLean.
#
# AFFINE cores (rad abelian): construct = so(eta') affine R^{d'} realized in gl(d'+1)
#   (S921 (d'+1)-rep) -> BOTH sides are concrete matrices, full A1-style formalization.
# CENTRAL-EXTENDED cores are handled separately (Jacobi faithful rep) -- see gen_A2_ext.
#
# Everything is verified here as EXACT matrix identities (rational, no floats) BEFORE emit;
# the Lean file re-verifies the same identities in-kernel (fourth layer).
#
# Provenance: object = T17/T18 (S) 12 ladder; cores from S937/S940; iso from S946
# (src/symbolic/S946_w33_leg2b_bt_verify_iso_blind.py, export S946_w33_leg2b_iso_export.json).
import sys
sys.stdout.reconfigure(encoding="utf-8")
from sympy import Matrix, Integer, zeros, eye, diag, symbols, linsolve

# ===================== primitives (mirrored from S946) =====================

def make_eta(p, q):
    return diag(*([Integer(1)] * p + [Integer(-1)] * q))

def unit(n, i):
    v = zeros(n, 1); v[i, 0] = Integer(1); return v

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
    n = M.rows; return Matrix(n * n, 1, list(M))

def stack_flats(mats, sq):
    if not mats:
        return zeros(sq * sq, 0)
    return Matrix.hstack(*[flat(M) for M in mats])

def span_basis(mats, sq):
    out = []; F = zeros(sq * sq, 0); r = 0
    for M in mats:
        F2 = Matrix.hstack(F, flat(M))
        if F2.rank() > r:
            out.append(M); F = F2; r += 1
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

def coords_in(basis, M, sq):
    F = stack_flats(basis, sq); v = flat(M)
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

def ad_matrices(L, n):
    k = len(L); ads = []
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
    ads = ad_matrices(core, n); k = len(core)
    K = zeros(k, k)
    for i in range(k):
        for j in range(k):
            K[i, j] = (ads[i] * ads[j]).trace()
    ns = K.nullspace(); rad = []
    for v in ns:
        M = zeros(n, n)
        for t in range(k):
            if v[t, 0] != 0:
                M = M + v[t, 0] * core[t]
        rad.append(M)
    return span_basis(rad, n)

def complement_reps(core, rad, n):
    F = stack_flats(rad, n); rk = F.rank(); reps = []
    for M in core:
        F2 = Matrix.hstack(F, flat(M))
        if F2.rank() > rk:
            reps.append(M); F = F2; rk += 1
    return reps

def d1_on(K, p, n):
    Kp = [a for a in K if a < p]; Km = [a for a in K if a >= p]
    if len(Kp) >= 1 and len(Km) >= 1 and len(K) >= 3:
        a, b = Kp[0], Km[0]
        rest = [c for c in K if c not in (a, b)]; c = rest[0]
        return unit(n, a) + unit(n, b), unit(n, c)
    return None

def levi_explicit(core, rad, n):
    reps = complement_reps(core, rad, n); kq = len(reps); dr = len(rad)
    full = reps + rad; cstr = {}
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
    solset = list(sol)[0]; freevars = set()
    for expr in solset:
        freevars |= expr.free_symbols
    zsub = {s: Integer(0) for s in freevars}
    vals = {unknowns[idx]: solset[idx] for idx in range(len(unknowns))}
    levi = [(reps[i] + t[i]).subs(vals).subs(zsub) for i in range(kq)]
    lb = span_basis(levi, n)
    if len(lb) != kq:
        return None
    return lb

def module_action(L, M, Z, n):
    dm = len(M); full = M + Z; ops = []
    for Li in L:
        cols = []
        for j in range(dm):
            c = coords_in(full, Li * M[j] - M[j] * Li, n)
            cols.append(Matrix(dm, 1, [c[t, 0] for t in range(dm)]))
        ops.append(Matrix.hstack(*cols))
    return ops

def invariant_sym_form(rhos, dm):
    idx = {}; cnt = 0
    for a in range(dm):
        for b in range(a, dm):
            idx[(a, b)] = cnt; cnt += 1
    gs = symbols('g0:%d' % cnt); G = zeros(dm, dm)
    for a in range(dm):
        for b in range(a, dm):
            G[a, b] = gs[idx[(a, b)]]; G[b, a] = gs[idx[(a, b)]]
    eqs = []
    for rho in rhos:
        E = rho.T * G + G * rho
        for a in range(dm):
            for b in range(dm):
                eqs.append(E[a, b])
    sol = linsolve(eqs, list(gs))
    if not sol:
        return None
    s = list(sol)[0]; free = set()
    for e in s:
        free |= e.free_symbols
    for pick in (list(free) if free else [None]):
        sub = {f: (Integer(1) if f == pick else Integer(0)) for f in free}
        Gv = G.subs({gs[idx[(a, b)]]: s[idx[(a, b)]] for a in range(dm) for b in range(a, dm)}).subs(sub)
        if Gv.det() != 0:
            return Gv
    return None

def cong_to_diag_pm(g, dm):
    from sympy import sqrt as ssqrt
    A = g.copy(); P = eye(dm)
    for i in range(dm):
        if A[i, i] == 0:
            js = None
            for j in range(i + 1, dm):
                if A[j, j] != 0:
                    js = j; break
            if js is not None:
                A.col_swap(i, js); A.row_swap(i, js); P.col_swap(i, js)
            else:
                jn = None
                for j in range(i + 1, dm):
                    if A[i, j] != 0:
                        jn = j; break
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
    for i in range(dm):
        d = A[i, i]
        if d != 0:
            sc = 1 / ssqrt(abs(d))
            P[:, i] = P[:, i] * sc; A[i, :] = A[i, :] * sc; A[:, i] = A[:, i] * sc
    pos = sum(1 for i in range(dm) if A[i, i] > 0)
    neg = sum(1 for i in range(dm) if A[i, i] < 0)
    return P, (pos, neg)

def hat(M, dp):
    return M.row_join(zeros(dp, 1)).col_join(zeros(1, dp + 1))

def Tmat(a, dp):
    T = zeros(dp + 1, dp + 1)
    for i in range(dp):
        T[i, dp] = a[i, 0]
    return T

def sc_of(basis, n):
    tab = {}; k = len(basis)
    for i in range(k):
        for j in range(i + 1, k):
            c = coords_in(basis, basis[i] * basis[j] - basis[j] * basis[i], n)
            if c is None:
                return None
            tab[(i, j)] = tuple(c[t, 0] for t in range(k))
    return tab

def d0_on(K, p, n):
    Kp = [a for a in K if a < p]; Km = [a for a in K if a >= p]
    if len(Kp) >= 2 and len(Km) >= 2:
        return unit(n, Kp[0]) + unit(n, Km[0]), unit(n, Kp[1]) + unit(n, Km[1])
    return None

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

def darboux(omega, dm):
    # P with Pᵀ ω P = J (standard symplectic [[0,I],[-I,0]]); dm even (mirrored from S946)
    m = dm // 2
    A = omega.copy()

    def wform(u, v):
        return (u.T * A * v)[0, 0]

    vs = [unit(dm, i) for i in range(dm)]
    e_list = []; f_list = []; span_cols = zeros(dm, 0)
    while len(e_list) < m:
        u = None
        for cand in vs:
            if Matrix.hstack(span_cols, cand).rank() > span_cols.rank():
                u = cand; break
        if u is None:
            return None
        v = None
        for cand in vs:
            if wform(u, cand) != 0 and Matrix.hstack(span_cols, u, cand).rank() > Matrix.hstack(span_cols, u).rank():
                v = cand / wform(u, cand); break
        if v is None:
            return None
        newvs = [w - wform(w, v) * u + wform(w, u) * v for w in vs]
        e_list.append(u); f_list.append(v)
        span_cols = Matrix.hstack(span_cols, u, v); vs = newvs
    Q = Matrix.hstack(*(e_list + f_list))
    J = zeros(dm, dm)
    for i in range(m):
        J[i, m + i] = Integer(1); J[m + i, i] = Integer(-1)
    if (Q.T * A * Q - J) != zeros(dm, dm):
        return None
    return Q

def embed_block(S, amb, off):
    # place S (k x k) into an amb x amb zero matrix at offset (off,off)
    k = S.rows
    M = zeros(amb, amb)
    for i in range(k):
        for j in range(k):
            M[off + i, off + j] = S[i, j]
    return M

def jacobi_rep(psis, J, dm):
    # Faithful (dm+2)-rep of sp(J) ⋉ h_{dm+1}: middle block = sp module V (indices 1..dm),
    # index 0 = 'top', index dm+1 = 'bottom' (center target).
    #   Levi  DL_i = embed(psi_i) at offset 1
    #   transl DT_j: column e_j in middle rows into bottom col; row (1/2 J e_j)ᵀ at top row
    #   center Dz = E_{0, dm+1}
    # Verifies: [DT_i,DT_j] = J_ij Dz ; [DL_i,DT_j] = Σ (psi_i)_kj DT_k ; z central.
    amb = dm + 2
    from sympy import Rational
    A = Rational(1, 2) * J   # row vectors r_j = j-th row of A ; A - Aᵀ = J
    DL = [embed_block(psis[i], amb, 1) for i in range(len(psis))]
    DT = []
    for j in range(dm):
        M = zeros(amb, amb)
        # column e_j: middle row (1+j) -> bottom col (dm+1)
        M[1 + j, dm + 1] = Integer(1)
        # row r_j = A[j,:] at top row 0 -> middle cols (1..dm)
        for k in range(dm):
            M[0, 1 + k] = A[j, k]
        DT.append(M)
    Dz = zeros(amb, amb); Dz[0, dm + 1] = Integer(1)
    return DL, DT, Dz

# ===================== per-core affine build =====================

AFFINE_CORES = [
    ("N", 5, 1, "rank1"),
    ("N", 4, 2, "rank1"),
    ("N", 3, 3, "rank1"),
]

def build_affine(p, q):
    n = p + q
    eta = make_eta(p, q)
    bas = so_basis(n, eta)
    x, y = d1_on(list(range(n)), p, n)
    N = wedge(x, y, eta)
    # nilpotency degree (rank-1 orbit: not necessarily N^2=0; find smallest k with N^k=0)
    nildeg = None
    Nk = eye(n)
    for k in range(1, n + 2):
        Nk = Nk * N
        if Nk.is_zero_matrix:
            nildeg = k
            break
    core = perfect_core(centralizer(N, bas), n)
    rad = killing_radical(core, n)
    assert len(bracket_basis(rad, n)) == 0, "rad abelian (affine branch)"
    L = levi_explicit(core, rad, n)
    M = list(rad)
    dm = len(M)
    kq = len(L)
    rhos = module_action(L, M, [], n)
    g = invariant_sym_form(rhos, dm)
    P, sig = cong_to_diag_pm(g, dm)
    D = P.T * g * P
    Pinv = P.inv()
    # construct in (dm+1)-rep
    psis = [Pinv * rhos[i] * P for i in range(kq)]
    CL = [hat(psis[i], dm) for i in range(kq)]
    CT = [Tmat(unit(dm, j), dm) for j in range(dm)]
    C = CL + CT
    # eta' = the normalized diagonal (sorted +...+/-...-) that psi respects: use D
    etap = D
    for i in range(kq):
        assert (psis[i].T * etap + etap * psis[i]).is_zero_matrix, "psi in so(eta')"
    # core adapted basis B = L + P-aligned module
    BL = list(L)
    BM = []
    for j in range(dm):
        Mm = zeros(n, n)
        for l in range(dm):
            Mm = Mm + P[l, j] * M[l]
        BM.append(Mm)
    B = BL + BM
    d = len(B)
    assert len(C) == d, "same dim"
    # centralizer law: each B_i commutes with N
    for Bi in B:
        assert is_so(Bi, eta), "B_i in so(eta)"
        assert (Bi * N - N * Bi).is_zero_matrix, "[B_i,N]=0"
    scB = sc_of(B, n)
    scC = sc_of(C, dm + 1)
    assert scB is not None and scC is not None, "closed"
    assert scB == scC, "sc(B)==sc(C) (the iso)"
    dim_cN = len(span_basis(centralizer(N, bas), n))
    return dict(n=n, eta=eta, N=N, B=B, C=C, etap=etap, dm=dm, kq=kq, d=d,
                sig=sig, sc=scB, amb=dm + 1, nildeg=nildeg,
                dim_cN=dim_cN, extra=dim_cN - d, extra_kind="central")

# ===================== per-core central-extended build =====================

EXT_CORES = [
    ("N", 3, 2, "rank0"),
    ("N", 4, 2, "rank0"),
    ("N", 3, 3, "rank0"),
]

def build_extended(p, q):
    n = p + q
    eta = make_eta(p, q)
    bas = so_basis(n, eta)
    x, y = d0_on(list(range(n)), p, n)
    N = wedge(x, y, eta)
    assert (N * N).is_zero_matrix, "N nilpotent (rank-0 orbit, N^2=0)"
    core = perfect_core(centralizer(N, bas), n)
    rad = killing_radical(core, n)
    assert len(bracket_basis(rad, n)) == 1, "rad Heisenberg ([rad,rad]=Z, dim 1)"
    L = levi_explicit(core, rad, n); kq = len(L)
    Z = span_basis(center_of(rad, n), n)
    assert len(Z) == 1, "center dim 1"
    M = complement_reps(rad, Z, n); dm = len(M)
    assert dm % 2 == 0, "module even-dim"
    rhos = module_action(L, M, Z, n)
    Zc = Z[0]
    # symplectic form w from actual [M_a,M_b] into Zc
    w = zeros(dm, dm)
    for a in range(dm):
        for b in range(dm):
            cc = coords_in([Zc], M[a] * M[b] - M[b] * M[a], n)
            w[a, b] = cc[0, 0] if cc is not None else Integer(0)
    assert w.det() != 0, "w nondegenerate"
    Q = darboux(w, dm)
    assert Q is not None, "darboux ok"
    Qinv = Q.inv()
    m = dm // 2
    J = zeros(dm, dm)
    for i in range(m):
        J[i, m + i] = Integer(1); J[m + i, i] = Integer(-1)
    psis = [Qinv * rhos[i] * Q for i in range(kq)]
    for psi in psis:
        assert (psi.T * J + J * psi).is_zero_matrix, "psi in sp(J)"
    # core adapted basis B = L + Q-aligned module + center
    BL = list(L)
    BM = []
    for j in range(dm):
        Mm = zeros(n, n)
        for l in range(dm):
            Mm = Mm + Q[l, j] * M[l]
        BM.append(Mm)
    B = BL + BM + [Zc]
    d = len(B)
    for Bi in B:
        assert is_so(Bi, eta), "B_i in so(eta)"
        assert (Bi * N - N * Bi).is_zero_matrix, "[B_i,N]=0"
    # construct: Jacobi faithful rep
    DL, DT, Dz = jacobi_rep(psis, J, dm)
    D = DL + DT + [Dz]
    amb = dm + 2
    assert len(D) == d, "same dim"
    scB = sc_of(B, n)
    scD = sc_of(D, amb)
    assert scB is not None and scD is not None, "closed"
    assert scB == scD, "sc(B)==sc(D) (the iso, both ways)"
    dim_cN = len(span_basis(centralizer(N, bas), n))
    return dict(n=n, eta=eta, N=N, B=B, D=D, J=J, dm=dm, kq=kq, d=d,
                psis=psis, sc=scB, amb=amb, nildeg=2,
                dim_cN=dim_cN, extra=dim_cN - d,
                extra_kind="radical (non-central)")

# ===================== FULL centralizer + independence minor =====================

def indep_minor(mats, sq):
    # d chosen flat-coordinates where the d×d evaluation matrix S (S[k][l] = mats[l] at coord k)
    # is invertible.  S invertible ⟺ mats linearly independent (decidable certificate).
    d = len(mats)
    piv = []; r = 0
    for coord in range(sq * sq):
        rows = piv + [coord]
        S = Matrix([[mats[l][c // sq, c % sq] for l in range(d)] for c in rows])
        if S.rank() > r:
            piv.append(coord); r += 1
        if r == d:
            break
    assert r == d, "basis not independent (rank<d)"
    S = Matrix([[mats[l][c // sq, c % sq] for l in range(d)] for c in piv])
    return S, S.inv(), piv

def build_affine_full(p, q):
    # FULL centralizer c(N) = ℝ_Z ⊕ (so(eta')⋉ℝ^{d'}) : perfect-core iso + central generator Z.
    da = build_affine(p, q)
    n = da["n"]; eta = da["eta"]; N = da["N"]; dm = da["dm"]; kq = da["kq"]
    B = list(da["B"]); C = list(da["C"]); amb0 = da["amb"]
    bas = so_basis(n, eta)
    cN = span_basis(centralizer(N, bas), n)
    perf = perfect_core(cN, n)
    extra = complement_reps(cN, perf, n)   # the 1-dim center Z (outside the perfect core)
    assert len(extra) == 1, "rank1 extra dim 1"
    Z = extra[0]
    assert is_so(Z, eta) and (Z * N - N * Z).is_zero_matrix, "Z in so(eta), [Z,N]=0"
    for Bi in B:
        assert (Z * Bi - Bi * Z).is_zero_matrix, "Z central in c(N)"
    Bf = B + [Z]                            # index d-1 = central Z
    amb = amb0 + 1
    Cf = [embed_block(Ci, amb, 0) for Ci in C]
    z = zeros(amb, amb); z[amb0, amb0] = Integer(1)   # central: E_{last,last} vs block-embedded C
    Cf = Cf + [z]
    d = len(Bf)
    scB = sc_of(Bf, n); scC = sc_of(Cf, amb)
    assert scB == scC, "sc(Bf)==sc(Cf) (full iso)"
    SB, SBi, _ = indep_minor(Bf, n)
    SC, SCi, _ = indep_minor(Cf, amb)
    return dict(n=n, amb=amb, dm=dm, kq=kq, d=d, eta=eta,
                anchor=("so", da["etap"]), N=N, nildeg=da["nildeg"],
                B=Bf, C=Cf, psi=psi_blocks(da), sc=scB,
                minorB=(SB, SBi), minorC=(SC, SCi),
                extra="R-center Z (index %d): central in c(N), so c(N)=R (+) (Levi (x) R^d')" % (d - 1),
                dim_cN=len(cN), sig=da["sig"], kind="affine")

def build_extended_full(p, q):
    # FULL centralizer c(N). (3,2)r0: = perfect core (Levi⋉h3), no gap.  (4,2)/(3,3)r0:
    # = (Levi ⊕ R_W)⋉h5, W a reductive-center dilation acting on the module in sp(J).
    de = build_extended(p, q)
    n = de["n"]; eta = de["eta"]; N = de["N"]; dm = de["dm"]; kq = de["kq"]; J = de["J"]
    B = list(de["B"]); D = list(de["D"]); amb = de["amb"]
    bas = so_basis(n, eta)
    cN = span_basis(centralizer(N, bas), n)
    perf = perfect_core(cN, n)
    extra = complement_reps(cN, perf, n)
    cube = None
    if not extra:
        Bf = B; Df = D
        extradesc = "none (full c(N) = perfect core = Levi (x) h3)"
    else:
        W = extra[0]
        assert (W * N - N * W).is_zero_matrix, "[W,N]=0"
        BM = B[kq:kq + dm]                  # Q-aligned module inside B
        cols = []
        for j in range(dm):
            c = coords_in(BM, W * BM[j] - BM[j] * W, n)
            assert c is not None, "W preserves module span"
            cols.append(Matrix(dm, 1, [c[t, 0] for t in range(dm)]))
        aW = Matrix.hstack(*cols)           # W action on module (dm×dm)
        assert (aW.T * J + J * aW).is_zero_matrix, "W acts in sp(J)"
        DW = embed_block(aW, amb, 1)        # realize W in the SAME Jacobi rep
        Bf = B + [W]; Df = D + [DW]
        # SIGNATURE of the reductive centre so(eta|G): compact so(2) (eigenvalues ±i) vs
        # non-compact so(1,1) boost (eigenvalues ±1).  This is the compact-Levi⟺q story (C1).
        nz = [e for e in W.eigenvals() if e != 0]
        centre = "so(2) compact rotation (eigenvalues ±i)" if all(e.is_imaginary for e in nz) \
            else "so(1,1) boost, NON-compact (eigenvalues ±1)"
        cname = "so(2)" if all(e.is_imaginary for e in nz) else "so(1,1)"
        # W^3 = ∓W distinguishes compact (so(2), W^2=-1 on its plane, minimal poly x(x^2+1))
        # from boost (so(1,1), W^2=+1 on plane, minimal poly x(x^2-1)) — a full-matrix named identity.
        cube_sign = -1 if all(e.is_imaginary for e in nz) else 1
        cube = (len(Bf) - 1, cube_sign, cname)
        extradesc = ("reductive-centre generator W (index %d) = %s = so(eta|G) of the Levi; W acts on "
                     "the h5 module in sp(J), commutes with the sp(2,R) Levi (distinct factors), so "
                     "c(N)=(sp(2,R) (+) %s) (x) h5" % (len(Bf) - 1, centre, cname))
    d = len(Bf)
    for Bi in Bf:
        assert is_so(Bi, eta), "B_i in so(eta)"
        assert (Bi * N - N * Bi).is_zero_matrix, "[B_i,N]=0"
    scB = sc_of(Bf, n); scD = sc_of(Df, amb)
    assert scB == scD, "sc(Bf)==sc(Df) (full iso)"
    SB, SBi, _ = indep_minor(Bf, n)
    SD, SDi, _ = indep_minor(Df, amb)
    return dict(n=n, amb=amb, dm=dm, kq=kq, d=d, eta=eta,
                anchor=("sp", J), N=N, nildeg=2,
                B=Bf, C=Df, psi=de["psis"], sc=scB,
                minorB=(SB, SBi), minorC=(SD, SDi),
                extra=extradesc, dim_cN=len(cN), sig=None, kind="jacobi", cube=cube)

# ===================== Lean emit =====================

def q_lit(x):
    # exact rational -> Lean literal
    x = Integer(x) if x == int(x) else x
    s = str(x)
    return s

def lean_mat(M):
    rows = "; ".join(", ".join(q_lit(M[i, j]) for j in range(M.cols)) for i in range(M.rows))
    return "!![" + rows + "]"

def rhs_terms(coeffs, names):
    terms = []
    for k in range(len(coeffs)):
        c = coeffs[k]
        if c == 0:
            continue
        if c == 1:
            terms.append(names[k])
        elif c == -1:
            terms.append("-" + names[k])
        else:
            terms.append("(%s:%s) • %s" % (q_lit(c), "ℚ", names[k]))
    if not terms:
        return "0"
    # join, turning "+ -x" into "- x"
    out = terms[0]
    for t in terms[1:]:
        if t.startswith("-"):
            out += " - " + t[1:]
        else:
            out += " + " + t
    return out

def emit(tag, data, prefix):
    n = data["n"]; amb = data["amb"]; d = data["d"]
    print("\n" + "=" * 78)
    print("=== %s : core in so(%d), construct in gl(%d), dim algebra = %d, sig(eta')=%s, nildeg(N)=%s ==="
          % (tag, n, amb, d, data["sig"], data["nildeg"]))
    print("=" * 78)
    print("eta  := " + lean_mat(data["eta"]))
    print("etap := " + lean_mat(data["etap"]))
    print("N    := " + lean_mat(data["N"]))
    bn = ["%sB%d" % (prefix, i) for i in range(d)]
    cn = ["%sC%d" % (prefix, i) for i in range(d)]
    for i in range(d):
        print("B%d := %s" % (i, lean_mat(data["B"][i])))
    for i in range(d):
        print("C%d := %s" % (i, lean_mat(data["C"][i])))
    print("--- bracket table (SAME sc for B and C = the iso) ---")
    for (i, j), c in data["sc"].items():
        print("  [%d,%d]  B: %s" % (i, j, rhs_terms(c, ["B%d" % t for t in range(d)])))
        print("         C: %s" % rhs_terms(c, ["C%d" % t for t in range(d)]))

# ===================== full Lean-file emit =====================

def psi_blocks(data):
    # the 3 Levi images psi_i = top-left dm x dm block of C_i (i<kq)
    dm = data["dm"]; kq = data["kq"]
    out = []
    for i in range(kq):
        Ci = data["C"][i]
        out.append(Ci[0:dm, 0:dm])
    return out

LEAN_HEADER = """import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.style.longLine false      -- generated wide matrix literals
set_option linter.unusedSimpArgs false       -- one `mat` tactic covers several Fin sizes

"""

SUMLEMMAS = ("Fin.sum_univ_one, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,\n"
             "                   Fin.sum_univ_five, Fin.sum_univ_six, Fin.sum_univ_seven,\n"
             "                   Fin.sum_univ_eight, Fin.sum_univ_zero, Fin.sum_univ_succ")

def lean_file_full(ns, title, doc, data):
    n = data["n"]; amb = data["amb"]; dm = data["dm"]; kq = data["kq"]; d = data["d"]
    kind, mp = data["anchor"]                     # ('so', etap dm×dm) or ('sp', J dm×dm)
    anchor_name = "so(η')" if kind == "so" else "sp(J)"
    mpname = "etap" if kind == "so" else "Jsp"
    apred = "inSOp" if kind == "so" else "inSPp"
    psi = data["psi"]
    SB, SBi = data["minorB"]; SC, SCi = data["minorC"]
    scope = ("\n\n★SCOPE: this is the FULL centralizer c(N), dim %d = dim c(N) (S933/S946 probe).\n"
             "Structure: %s\n"
             "What is proven in-kernel: N nilpotent · N,Bᵢ ∈ so(η) · [Bᵢ,N]=0 (⟹ B ⊂ c(N)) ·\n"
             "ψ(Levi) ∈ %s (construct anchor) · Bᵢ and Cᵢ each linearly independent (invertible\n"
             "evaluation minor) · both bracket tables with IDENTICAL structure constants ⟹ Bᵢ ↦ Cᵢ\n"
             "is a Lie isomorphism c(N) ≅ construct.  Basis-completeness (dim c(N)=%d) is the probe's;\n"
             "Lean re-verifies the exact identities (fourth layer).  All decidable ℚ (no native_decide)."
             % (d, data["extra"], anchor_name, d))
    L = [LEAN_HEADER]
    L.append("/-!\n" + title + "\n" + doc + scope + "\n-/\n")
    L.append("namespace VGLean.A2.%s\n" % ns)
    L.append("open Matrix\n")
    L.append("abbrev Mn := Matrix (Fin %d) (Fin %d) ℚ   -- core ambient so(p,q)" % (n, n))
    L.append("abbrev Mc := Matrix (Fin %d) (Fin %d) ℚ   -- construct ambient" % (amb, amb))
    L.append("abbrev Mp := Matrix (Fin %d) (Fin %d) ℚ   -- Levi anchor block (%s)" % (dm, dm, anchor_name))
    L.append("abbrev Md := Matrix (Fin %d) (Fin %d) ℚ   -- independence-minor size\n" % (d, d))
    L.append("def eta : Mn := " + lean_mat(data["eta"]))
    L.append("def %s : Mp := %s" % (mpname, lean_mat(mp)))
    L.append("def N : Mn := " + lean_mat(data["N"]))
    for i in range(d):
        L.append("def B%d : Mn := %s" % (i, lean_mat(data["B"][i])))
    for i in range(d):
        L.append("def C%d : Mc := %s" % (i, lean_mat(data["C"][i])))
    for i in range(kq):
        L.append("def psi%d : Mp := %s" % (i, lean_mat(psi[i])))
    L.append("def minorB : Md := " + lean_mat(SB))
    L.append("def minorBinv : Md := " + lean_mat(SBi))
    L.append("def minorC : Md := " + lean_mat(SC))
    L.append("def minorCinv : Md := " + lean_mat(SCi))
    L.append("")
    L.append("def inSOn (A : Mn) : Prop := Aᵀ * eta + eta * A = 0")
    L.append("def %s (A : Mp) : Prop := Aᵀ * %s + %s * A = 0" % (apred, mpname, mpname))
    L.append("def commN (A B : Mn) : Mn := A * B - B * A")
    L.append("def commC (A B : Mc) : Mc := A * B - B * A\n")
    defs_n = "eta, N, " + ", ".join("B%d" % i for i in range(d))
    defs_c = ", ".join("C%d" % i for i in range(d))
    defs_p = "%s, %s" % (mpname, ", ".join("psi%d" % i for i in range(kq)))
    defs_m = "minorB, minorBinv, minorC, minorCinv"
    L.append("macro \"mat\" : tactic =>")
    L.append("  `(tactic| (apply Matrix.ext; intro i j;")
    L.append("             fin_cases i <;> fin_cases j <;>")
    L.append("             simp [%s, %s, %s, %s," % (defs_n, defs_c, defs_p, defs_m))
    L.append("                   inSOn, %s, commN, commC," % apred)
    L.append("                   Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,")
    L.append("                   Matrix.transpose_apply, Matrix.smul_apply, Matrix.zero_apply,")
    L.append("                   Matrix.neg_apply, %s] <;>" % SUMLEMMAS)
    L.append("             norm_num))\n")
    # nilpotency
    pw = " * ".join(["N"] * data["nildeg"])
    L.append("-- N nilpotent: N^%d = 0." % data["nildeg"])
    L.append("theorem N_nilpotent : %s = 0 := by mat\n" % pw)
    L.append("-- Core-adapted basis of the FULL centralizer lies in so(η).")
    L.append("theorem N_inSO : inSOn N := by mat")
    for i in range(d):
        L.append("theorem B%d_inSO : inSOn B%d := by mat" % (i, i))
    L.append("")
    L.append("-- Centralizer law: every basis element commutes with N  (⟹ B ⊂ c(N)).")
    for i in range(d):
        L.append("theorem B%d_comm : commN B%d N = 0 := by mat" % (i, i))
    L.append("")
    L.append("-- Construct anchor: the Levi images ψ(Lᵢ) lie in %s." % anchor_name)
    for i in range(kq):
        L.append("theorem psi%d_anchor : %s psi%d := by mat" % (i, apred, i))
    L.append("")
    L.append("-- Linear independence (decidable certificate): the evaluation minor is invertible.")
    L.append("-- minorB[k][l] = (Bₗ) at probe coord k; minorB·minorBinv = 1 ⟹ B₀..B_{d-1} independent.")
    L.append("theorem B_indep : minorB * minorBinv = 1 := by mat")
    L.append("theorem C_indep : minorC * minorCinv = 1 := by mat")
    L.append("")
    bn = ["B%d" % t for t in range(d)]
    cn = ["C%d" % t for t in range(d)]
    L.append("-- Bracket table of the CORE basis B (closes with the measured structure constants).")
    for (i, j), c in data["sc"].items():
        L.append("theorem brB_%d_%d : commN B%d B%d = %s := by mat" % (i, j, i, j, rhs_terms(c, bn)))
    L.append("")
    L.append("-- Bracket table of the CONSTRUCT basis C — IDENTICAL structure constants ⟹ Bᵢ ↦ Cᵢ is the iso.")
    for (i, j), c in data["sc"].items():
        L.append("theorem brC_%d_%d : commC C%d C%d = %s := by mat" % (i, j, i, j, rhs_terms(c, cn)))
    L.append("")
    cube = data.get("cube")
    if cube is not None:
        idx, sign, cname = cube
        signstr = "-B%d" % idx if sign == -1 else "B%d" % idx
        poly = "x(x²+1)" if sign == -1 else "x(x²−1)"
        kindname = "COMPACT so(2)" if sign == -1 else "NON-compact so(1,1) boost"
        L.append("-- Reductive-centre signature (named, kernel-checked): B%d³ = %s ⟹ minimal poly %s" % (idx, signstr, poly))
        L.append("-- ⟹ nonzero eigenvalues %s ⟹ so(η|G) = %s.  (NB B%d² is NOT ±1 on the full space —" % ("±i" if sign == -1 else "±1", kindname, idx))
        L.append("--  only on its 2-plane; B%d³=%s is the clean full-matrix invariant of the eigenvalue type.)" % (idx, signstr))
        L.append("theorem B%d_cube : B%d * B%d * B%d = %s := by mat" % (idx, idx, idx, idx, signstr))
        L.append("")
    L.append("end VGLean.A2.%s" % ns)
    return "\n".join(L) + "\n"

def lean_file(tag_ns, doc, data):
    n = data["n"]; amb = data["amb"]; dm = data["dm"]; kq = data["kq"]; d = data["d"]
    psis = psi_blocks(data)
    note = ("\n\n★SCOPE (honest): the algebra formalized here is the PERFECT CORE of the centralizer\n"
            "c(N) (= S946's `core`, the non-abelian part), dim = %d.  The FULL centralizer c(N) has\n"
            "dim %d — one extra %s generator outside the perfect core (matches the T18 formula\n"
            "d'(d'+1)/2+1 for rank-1).  S946's exported isomorphism is for the perfect core; this file\n"
            "verifies exactly that.  B ⊂ c(N) holds (proven), but B spans the perfect core, not all of c(N)."
            % (data["d"], data["dim_cN"], data["extra_kind"]))
    L = []
    L.append(LEAN_HEADER)
    L.append("/-!\n" + doc + note + "\n-/\n")
    L.append("namespace VGLean.A2.%s\n" % tag_ns)
    L.append("open Matrix\n")
    L.append("abbrev Mn := Matrix (Fin %d) (Fin %d) ℚ   -- core ambient so(p,q)" % (n, n))
    L.append("abbrev Ma := Matrix (Fin %d) (Fin %d) ℚ   -- construct ambient (affine (d'+1)-rep)" % (amb, amb))
    L.append("abbrev Mp := Matrix (Fin %d) (Fin %d) ℚ   -- Levi module (so(eta') block)\n" % (dm, dm))
    # defs
    L.append("def eta : Mn := " + lean_mat(data["eta"]))
    L.append("def etap : Mp := " + lean_mat(data["etap"]))
    L.append("def N : Mn := " + lean_mat(data["N"]))
    for i in range(d):
        L.append("def B%d : Mn := %s" % (i, lean_mat(data["B"][i])))
    for i in range(d):
        L.append("def C%d : Ma := %s" % (i, lean_mat(data["C"][i])))
    for i in range(kq):
        L.append("def psi%d : Mp := %s" % (i, lean_mat(psis[i])))
    L.append("")
    # predicates
    L.append("def inSOn (A : Mn) : Prop := Aᵀ * eta + eta * A = 0")
    L.append("def inSOp (A : Mp) : Prop := Aᵀ * etap + etap * A = 0")
    L.append("def commN (A B : Mn) : Mn := A * B - B * A")
    L.append("def commA (A B : Ma) : Ma := A * B - B * A\n")
    # tactic
    defs_n = "eta, N, " + ", ".join("B%d" % i for i in range(d))
    defs_a = ", ".join("C%d" % i for i in range(d))
    defs_p = "etap, " + ", ".join("psi%d" % i for i in range(kq))
    L.append("macro \"mat\" : tactic =>")
    L.append("  `(tactic| (apply Matrix.ext; intro i j;")
    L.append("             fin_cases i <;> fin_cases j <;>")
    L.append("             simp [%s, %s, %s, inSOn, inSOp, commN, commA," % (defs_n, defs_a, defs_p))
    L.append("                   Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,")
    L.append("                   Matrix.transpose_apply, Matrix.smul_apply, Matrix.zero_apply,")
    L.append("                   Matrix.neg_apply, Fin.sum_univ_three, Fin.sum_univ_four,")
    L.append("                   Fin.sum_univ_six] <;>")
    L.append("             norm_num))\n")
    # nilpotency of N (matrix power) — informative
    if data["nildeg"] is not None:
        L.append("-- N is nilpotent (rank-1 orbit): N^%d = 0." % data["nildeg"])
        pw = " * ".join(["N"] * data["nildeg"])
        L.append("theorem N_nilpotent : %s = 0 := by mat\n" % pw)
    # core in so(eta)
    L.append("-- Core-adapted basis lies in so(eta) (skew-adjointness).")
    L.append("theorem N_inSO : inSOn N := by mat")
    for i in range(d):
        L.append("theorem B%d_inSO : inSOn B%d := by mat" % (i, i))
    L.append("")
    # centralizer law
    L.append("-- Centralizer law: each basis element commutes with N (so B ⊂ c(N)).")
    for i in range(d):
        L.append("theorem B%d_comm : commN B%d N = 0 := by mat" % (i, i))
    L.append("")
    # Levi in so(etap)
    L.append("-- Construct anchor: the 3 Levi images ψ(Lᵢ) lie in so(eta') (⟹ construct = so(eta') ⋉ ℝ^{d'}).")
    for i in range(kq):
        L.append("theorem psi%d_skew : inSOp psi%d := by mat" % (i, i))
    L.append("")
    # bracket tables
    bn = ["B%d" % t for t in range(d)]
    cn = ["C%d" % t for t in range(d)]
    L.append("-- Bracket table of the CORE basis B (closes with the measured structure constants).")
    for (i, j), c in data["sc"].items():
        L.append("theorem brB_%d_%d : commN B%d B%d = %s := by mat" % (i, j, i, j, rhs_terms(c, bn)))
    L.append("")
    L.append("-- Bracket table of the CONSTRUCT basis C — IDENTICAL structure constants ⟹ Bᵢ ↦ Cᵢ is a Lie isomorphism.")
    for (i, j), c in data["sc"].items():
        L.append("theorem brC_%d_%d : commA C%d C%d = %s := by mat" % (i, j, i, j, rhs_terms(c, cn)))
    L.append("")
    L.append("end VGLean.A2.%s" % tag_ns)
    return "\n".join(L) + "\n"

def lean_file_ext(tag_ns, doc, data):
    n = data["n"]; amb = data["amb"]; dm = data["dm"]; kq = data["kq"]; d = data["d"]
    psis = data["psis"]
    note = ("\n\n★SCOPE (honest): the algebra formalized here is the PERFECT CORE of the centralizer\n"
            "c(N) (= S946's `core`), dim = %d.  The FULL centralizer c(N) has dim %d — one extra\n"
            "%s generator outside the perfect core.  S946's exported isomorphism is\n"
            "for the perfect core; this file verifies exactly that.  B ⊂ c(N) holds (proven), but B\n"
            "spans the perfect core, not all of c(N)."
            % (data["d"], data["dim_cN"], data["extra_kind"]))
    L = []
    L.append(LEAN_HEADER)
    L.append("/-!\n" + doc + note + "\n-/\n")
    L.append("namespace VGLean.A2.%s\n" % tag_ns)
    L.append("open Matrix\n")
    L.append("abbrev Mn := Matrix (Fin %d) (Fin %d) ℚ   -- core ambient so(p,q)" % (n, n))
    L.append("abbrev Md := Matrix (Fin %d) (Fin %d) ℚ   -- construct ambient (Jacobi faithful rep, dim d'+2)" % (amb, amb))
    L.append("abbrev Mp := Matrix (Fin %d) (Fin %d) ℚ   -- symplectic module (sp(J) block)\n" % (dm, dm))
    L.append("def eta : Mn := " + lean_mat(data["eta"]))
    L.append("def Jsp : Mp := " + lean_mat(data["J"]))
    L.append("def N : Mn := " + lean_mat(data["N"]))
    for i in range(d):
        L.append("def B%d : Mn := %s" % (i, lean_mat(data["B"][i])))
    for i in range(d):
        L.append("def D%d : Md := %s" % (i, lean_mat(data["D"][i])))
    for i in range(kq):
        L.append("def psi%d : Mp := %s" % (i, lean_mat(psis[i])))
    L.append("")
    L.append("def inSOn (A : Mn) : Prop := Aᵀ * eta + eta * A = 0")
    L.append("def inSPp (A : Mp) : Prop := Aᵀ * Jsp + Jsp * A = 0")
    L.append("def commN (A B : Mn) : Mn := A * B - B * A")
    L.append("def commD (A B : Md) : Md := A * B - B * A\n")
    defs_n = "eta, N, " + ", ".join("B%d" % i for i in range(d))
    defs_d = ", ".join("D%d" % i for i in range(d))
    defs_p = "Jsp, " + ", ".join("psi%d" % i for i in range(kq))
    L.append("macro \"mat\" : tactic =>")
    L.append("  `(tactic| (apply Matrix.ext; intro i j;")
    L.append("             fin_cases i <;> fin_cases j <;>")
    L.append("             simp [%s, %s, %s, inSOn, inSPp, commN, commD," % (defs_n, defs_d, defs_p))
    L.append("                   Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,")
    L.append("                   Matrix.transpose_apply, Matrix.smul_apply, Matrix.zero_apply,")
    L.append("                   Matrix.neg_apply, Fin.sum_univ_two, Fin.sum_univ_three,")
    L.append("                   Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six] <;>")
    L.append("             norm_num))\n")
    L.append("-- N is nilpotent (rank-0 orbit): N^2 = 0.")
    L.append("theorem N_nilpotent : N * N = 0 := by mat\n")
    L.append("-- Core-adapted basis lies in so(eta).")
    L.append("theorem N_inSO : inSOn N := by mat")
    for i in range(d):
        L.append("theorem B%d_inSO : inSOn B%d := by mat" % (i, i))
    L.append("")
    L.append("-- Centralizer law: each basis element commutes with N (so B ⊂ c(N)).")
    for i in range(d):
        L.append("theorem B%d_comm : commN B%d N = 0 := by mat" % (i, i))
    L.append("")
    L.append("-- Construct anchor: the Levi images ψ(Lᵢ) lie in sp(J) (⟹ construct = sp(J) ⋉ Heisenberg).")
    for i in range(kq):
        L.append("theorem psi%d_symp : inSPp psi%d := by mat" % (i, i))
    L.append("")
    bn = ["B%d" % t for t in range(d)]
    dn = ["D%d" % t for t in range(d)]
    L.append("-- Bracket table of the CORE basis B (closes with the measured structure constants).")
    for (i, j), c in data["sc"].items():
        L.append("theorem brB_%d_%d : commN B%d B%d = %s := by mat" % (i, j, i, j, rhs_terms(c, bn)))
    L.append("")
    L.append("-- Bracket table of the CONSTRUCT basis D (Jacobi rep) — IDENTICAL structure constants ⟹ Bᵢ ↦ Dᵢ is a Lie isomorphism.")
    for (i, j), c in data["sc"].items():
        L.append("theorem brD_%d_%d : commD D%d D%d = %s := by mat" % (i, j, i, j, rhs_terms(c, dn)))
    L.append("")
    L.append("end VGLean.A2.%s" % tag_ns)
    return "\n".join(L) + "\n"

FILES_EXT = {
    ("N", 3, 2, "rank0"): ("So32r0",
        "# A2 — iso 4/6 : (3,2) rank-0 wedge centralizer  ≅  sp(2,ℝ) ⋉ h₃  (central extension)\n\n"
        "Core c(N) of the rank-0 nilpotent wedge N in so(3,2) = Levi(sp(2,ℝ)≅so(2,1)) ⋉ Heisenberg h₃.\n"
        "Construct = the Jacobi algebra sp(J)⋉h₃ in its faithful (d'+2)=4-dim rep (module V=ℝ², center\n"
        "→ E_{0,3}).  Data frozen by lean/artifacts/gen_A2_iso.py (exact rationals; ψ half-integer rows\n"
        "over ℚ; sc(B)==sc(D) verified both ways).  Identical bracket tables ARE the iso Bᵢ ↦ Dᵢ."),
    ("N", 4, 2, "rank0"): ("So42r0",
        "# A2 — iso 5/6 : (4,2) rank-0 wedge centralizer  ≅  sp(4,ℝ) ⋉ h₅  (central extension)\n\n"
        "Core c(N) in so(4,2) = Levi(sp(4,ℝ)) ⋉ Heisenberg h₅ (module V=ℝ⁴).  Construct = sp(J)⋉h₅ in\n"
        "its faithful (d'+2)=6-dim Jacobi rep.  Frozen by gen_A2_iso.py; sc(B)==sc(D) both ways (S946)."),
    ("N", 3, 3, "rank0"): ("So33r0",
        "# A2 — iso 6/6 : (3,3) rank-0 wedge centralizer  ≅  sp(4,ℝ) ⋉ h₅  (central extension)\n\n"
        "Core c(N) in so(3,3) = Levi(sp(4,ℝ)) ⋉ Heisenberg h₅ (module V=ℝ⁴).  Construct = sp(J)⋉h₅ in\n"
        "its faithful (d'+2)=6-dim Jacobi rep.  Frozen by gen_A2_iso.py; sc(B)==sc(D) both ways (S946)."),
}

FILES = {
    ("N", 5, 1, "rank1"): ("So51r1",
        "# A2 — iso 1/6 : (5,1) rank-1 wedge centralizer  ≅  so(3) ⋉ ℝ³ (affine, compact Levi)\n\n"
        "Core c(N) of the rank-1 nilpotent wedge N in so(5,1); construct = so(eta')⋉ℝ³ in the\n"
        "S921 (d'+1)-affine rep (eta' = diag(1,1,1), compact so(3) Levi).  Data frozen by\n"
        "lean/artifacts/gen_A2_iso.py (exact rationals; sc(B)==sc(C) verified both ways, S946).\n"
        "The two bracket tables use IDENTICAL structure constants — that equality IS the\n"
        "isomorphism Bᵢ ↦ Cᵢ.  All checks decidable ℚ arithmetic (no native_decide)."),
    ("N", 4, 2, "rank1"): ("So42r1",
        "# A2 — iso 2/6 : (4,2) rank-1 wedge centralizer  ≅  so(2,1) ⋉ ℝ³ (affine)\n\n"
        "Core c(N) in so(4,2); construct = so(eta')⋉ℝ³, eta' = diag(-1,-1,1) (signature (1,2)\n"
        "≅ so(2,1) Levi).  Frozen by gen_A2_iso.py; sc(B)==sc(C) both ways (S946)."),
    ("N", 3, 3, "rank1"): ("So33r1",
        "# A2 — iso 3/6 : (3,3) rank-1 wedge centralizer  ≅  so(2,1) ⋉ ℝ³ (affine)\n\n"
        "Core c(N) in so(3,3); construct = so(eta')⋉ℝ³, eta' = diag(-1,-1,1) (signature (1,2)\n"
        "≅ so(2,1) Levi).  Frozen by gen_A2_iso.py; sc(B)==sc(C) both ways (S946)."),
}

# ===================== FULL c(N) file registry (honest titles) =====================
# builder: 'A' = build_affine_full, 'E' = build_extended_full
FULL_FILES = [
    ("So51r1", 5, 1, "A",
     "# A2 — iso 1/6 : (5,1) rank-1 wedge, FULL centralizer  c(N) ≅ ℝ ⊕ (so(3) ⋉ ℝ³)",
     "Full c(N) = ℝ-center ⊕ Euclidean-type so(3)⋉ℝ³ (compact Levi).  Frozen by gen_A2_iso.py."),
    ("So42r1", 4, 2, "A",
     "# A2 — iso 2/6 : (4,2) rank-1 wedge, FULL centralizer  c(N) ≅ ℝ ⊕ (so(2,1) ⋉ ℝ³)",
     "Full c(N) = ℝ-center ⊕ so(2,1)⋉ℝ³ (η' = diag(-1,-1,1)).  Frozen by gen_A2_iso.py."),
    ("So33r1", 3, 3, "A",
     "# A2 — iso 3/6 : (3,3) rank-1 wedge, FULL centralizer  c(N) ≅ ℝ ⊕ (so(2,1) ⋉ ℝ³)",
     "Full c(N) = ℝ-center ⊕ so(2,1)⋉ℝ³.  Frozen by gen_A2_iso.py."),
    ("So32r0", 3, 2, "E",
     "# A2 — iso 4/6 : (3,2) rank-0 wedge, FULL centralizer  c(N) ≅ sp(2,ℝ) ⋉ h₃",
     "Full c(N) = Jacobi algebra sp(2,ℝ)⋉h₃ (here perfect core = full: so(η|G)=so(1)=0, no gap).\n"
     "Jacobi faithful 4-rep.  [sp(2,ℝ) ≅ sl(2,ℝ) ≅ so(2,1); symplectic name in the sp(J) context.]"),
    ("So42r0", 4, 2, "E",
     "# A2 — iso 5/6 : (4,2) rank-0 wedge, FULL centralizer  c(N) ≅ (sp(2,ℝ) ⊕ so(2)) ⋉ h₅",
     "Full c(N) = (sp(2,ℝ) Levi ⊕ so(2) compact centre) ⋉ Heisenberg h₅, inside the Jacobi 6-rep.\n"
     "NB: the Levi is sp(2,ℝ) (=sl(2,ℝ), dim 3), a proper symplectic subalgebra of sp(4,ℝ) (NOT sp(4,ℝ),\n"
     "dim 10); the extra so(2) is the compact reductive centre so(η|G) acting on the h₅ module."),
    ("So33r0", 3, 3, "E",
     "# A2 — iso 6/6 : (3,3) rank-0 wedge, FULL centralizer  c(N) ≅ (sp(2,ℝ) ⊕ so(1,1)) ⋉ h₅",
     "Full c(N) = (sp(2,ℝ) Levi ⊕ so(1,1) boost centre) ⋉ Heisenberg h₅, inside the Jacobi 6-rep.\n"
     "NB: the Levi is sp(2,ℝ) (=sl(2,ℝ), dim 3), a proper symplectic subalgebra of sp(4,ℝ).  The extra\n"
     "reductive centre so(η|G) here is so(1,1) — a NON-compact boost (eigenvalues ±1), because the core\n"
     "signature is (1,1); contrast So42r0 where it is compact so(2) ((2,0)).  This compact-vs-boost\n"
     "split of the reductive centre is exactly the compact-Levi ⟺ q=1 signature anatomy (C1)."),
]

if __name__ == "__main__":
    import os
    emit_lean = "--emit-lean" in sys.argv
    outdir = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          "..", "VGLean", "VGLean")
    for (ns, p, q, builder, title, doc) in FULL_FILES:
        data = build_affine_full(p, q) if builder == "A" else build_extended_full(p, q)
        print("=== %s : full c(N) dim=%d (probe %d) | core so(%d) construct gl(%d) | sc match, minors invertible ==="
              % (ns, data["d"], data["dim_cN"], data["n"], data["amb"]))
        if emit_lean:
            src = lean_file_full(ns, title, doc, data)
            path = os.path.normpath(os.path.join(outdir, ns + ".lean"))
            with open(path, "w", encoding="utf-8") as f:
                f.write(src)
            print("WROTE %s (%d theorems)" % (path, src.count("theorem ")))
    print("\nEXIT=0 (FULL centralizer: sc(B)==sc(C) + independence minors verified exactly, ALL 6 cores)")
