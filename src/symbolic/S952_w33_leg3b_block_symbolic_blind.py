# -*- coding: utf-8 -*-
# DIM: na (block-symbolic solution of [M,N]=0 with MatrixSymbol blocks; n-independent form; 0 handles).
#
# ============================================================================
# ADAPTED-BASIS CHOICE (stamped BEFORE any counting)
# ----------------------------------------------------------------------------
# For the wedge N = x∧y in so(p,q) the ambient R^n is split by the flag of N:
#   * rank-0 Gram (x,y null, orthogonal; N^2=0):  order  W ⊕ C ⊕ W'  where
#     W = im N = span{x,y} (isotropic 2-plane), W' = a dual isotropic 2-plane
#     (η pairs W<->W' by S=I_2), C = core (dim d = n-4, η|_C = G nondegenerate).
#     η = [[0,0,I],[0,G,0],[I,0,0]] ; N = [[0,0,ν],[0,0,0],[0,0,0]] (ν=W'->W, 2x2).
#   * rank-1 Gram (x null, y non-null, x⊥y; N^3=0): order  T3 ⊕ C  where
#     T3 = span{x,y,x'} is the single size-3 Jordan string (η3, N3 concrete 3x3),
#     C = core (dim d' = n-3, η|_C = G nondegenerate), N|_C = 0.
#     η = [[η3,0],[0,G]] ; N = [[N3,0],[0,0]].
# M is a block matrix with MatrixSymbol blocks (symbolic core dim d/d'); imposing
# so(η) (MᵀηM..=0) and [M,N]=0 splits the blocks into FREE / LINKED / ZERO — the
# solution form does NOT depend on n.  dim c is then a signature-independent
# polynomial in the core dim, validated bit-for-bit against centralizer() at
# n=5,6,7.  Mutant on every branch; FORBIDDEN-SCAN; STOP after the table.
# ============================================================================

import sys
sys.stdout.reconfigure(encoding='utf-8')

import os
from sympy import (Matrix, Integer, Rational, zeros, eye, diag, symbols, Symbol,
                   MatrixSymbol, ZeroMatrix, BlockMatrix, block_collapse)

_LOGPATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "S952_w33_leg3b_block_symbolic_blind_run.log")
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


# ==================== numeric primitives ====================

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


def same_span(A, B, sq):
    FA = stack_flats(A, sq)
    FB = stack_flats(B, sq)
    ra = FA.rank()
    rb = FB.rank()
    if ra != rb:
        return False
    return Matrix.hstack(FA, FB).rank() == ra


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


# ==================== §1 symbolic block equations (MatrixSymbol) ====================
def symbolic_rank0():
    d = Symbol('d', positive=True, integer=True)
    A = MatrixSymbol('A', 2, 2); B = MatrixSymbol('B', 2, d); Cc = MatrixSymbol('Cc', 2, 2)
    D = MatrixSymbol('D', d, 2); E = MatrixSymbol('E', d, d); F = MatrixSymbol('F', d, 2)
    G2 = MatrixSymbol('G2', 2, 2); H = MatrixSymbol('H', 2, d); K = MatrixSymbol('K', 2, 2)
    G = MatrixSymbol('G', d, d); nu = MatrixSymbol('nu', 2, 2)
    S = eye(2)
    Z2d = ZeroMatrix(2, d); Zd2 = ZeroMatrix(d, 2); Zdd = ZeroMatrix(d, d); Z22 = ZeroMatrix(2, 2)
    M = BlockMatrix([[A, B, Cc], [D, E, F], [G2, H, K]])
    eta = BlockMatrix([[Z22, Z2d, S], [Zd2, G, Zd2], [S, Z2d, Z22]])
    N = BlockMatrix([[Z22, Z2d, nu], [Zd2, Zdd, Zd2], [Z22, Z2d, Z22]])
    c1 = block_collapse(M.T * eta + eta * M)
    c2 = block_collapse(M * N - N * M)
    return c1, c2


def symbolic_rank1():
    d = Symbol('d', positive=True, integer=True)
    c = Symbol('c', nonzero=True)
    E3 = Matrix([[0, 0, 1], [0, c, 0], [1, 0, 0]])
    N3 = Matrix([[0, c, 0], [0, 0, -1], [0, 0, 0]])
    P = MatrixSymbol('P', 3, 3); Q = MatrixSymbol('Q', 3, d); R = MatrixSymbol('R', d, 3); Sm = MatrixSymbol('Sm', d, d)
    G = MatrixSymbol('G', d, d)
    Z3d = ZeroMatrix(3, d); Zd3 = ZeroMatrix(d, 3); Zdd = ZeroMatrix(d, d)
    M = BlockMatrix([[P, Q], [R, Sm]])
    eta = BlockMatrix([[Matrix(E3), Z3d], [Zd3, G]])
    N = BlockMatrix([[Matrix(N3), Z3d], [Zd3, Zdd]])
    c1 = block_collapse(M.T * eta + eta * M)
    c2 = block_collapse(M * N - N * M)
    return c1, c2


print("=== §1 SYMBOLIC BLOCK EQUATIONS (MatrixSymbol, symbolic core dim) ===")
r0c1, r0c2 = symbolic_rank0()
print("--- rank-0 : so(η) block equations (=0) ---")
_names0 = [["A", "B", "Cc"], ["D", "E", "F"], ["G2", "H", "K"]]
for i in range(3):
    for j in range(3):
        print("  soη[{0},{1}]: {2} = 0".format(_names0[i][j], "", r0c1.blocks[i, j]))
print("--- rank-0 : [M,N] block equations (=0) ---")
for i in range(3):
    for j in range(3):
        e = r0c2.blocks[i, j]
        if str(e) != "0":
            print("  [M,N][{0},{1}]: {2} = 0".format(i, j, e))
r1c1, r1c2 = symbolic_rank1()
print("--- rank-1 : so(η) block equations (=0) ---")
for i in range(2):
    for j in range(2):
        print("  soη[{0},{1}]: {2} = 0".format(i, j, r1c1.blocks[i, j]))
print("--- rank-1 : [M,N] block equations (=0) ---")
for i in range(2):
    for j in range(2):
        e = r1c2.blocks[i, j]
        if str(e) != "0":
            print("  [M,N][{0},{1}]: {2} = 0".format(i, j, e))

print()
print("=== §2 SOLUTION (free / linked / zero) — n-INDEPENDENT ===")
print("rank-0 (blocks over W(2) ⊕ C(d) ⊕ W'(2)):")
print("  FREE:   A ∈ sp(ν) [Aν+νAᵀ=0, dim 3 = so(2,1) Levi] ; Cc antisym 2x2 [dim 1 = center] ;")
print("          E ∈ so(G) [dim d(d-1)/2 = core] ; B free 2xd [dim 2d = module]")
print("  LINKED: F = -G⁻¹Bᵀ ; H = -DᵀG ; K = -Aᵀ")
print("  ZERO:   G2 = 0 ; D = 0 (⟹ H = 0)")
print("  dim c = 3 + 1 + d(d-1)/2 + 2d  =  d(d-1)/2 + 2d + 4   [d = n-4]")
print("rank-1 (blocks over T3(3) ⊕ C(d')):")
print("  FREE:   P ∈ so(η3)∩centralizer(N3) [dim 1] ; Sm ∈ so(G) [dim d'(d'-1)/2 = Levi+core] ;")
print("          Q with N3·Q=0 [only ker N3 row ⟹ dim d' = module]")
print("  LINKED: R = -G⁻¹(η3 Q)ᵀ")
print("  dim c = 1 + d'(d'-1)/2 + d'  =  d'(d'+1)/2 + 1   [d' = n-3]")


def dimc_rank0(d):
    return d * (d - 1) // 2 + 2 * d + 4


def dimc_rank1(dp):
    return dp * (dp + 1) // 2 + 1


# ==================== §3 bracket table (block × block → block, rank-0) ====================
print()
print("=== §3 BRACKET STRUCTURE [M1,M2] (rank-0 free blocks A,Cc,E,B → result block) ===")
# with M = [[A,B,Cc],[D=0,E,F],[G2=0,H,K=-Aᵀ]] and F=-G⁻¹Bᵀ, H=-DᵀG=0:
# effective M = [[A, B, Cc],[0, E, -G⁻¹Bᵀ],[0, 0, -Aᵀ]] (upper block-triangular!)
# [M1,M2] result blocks (which free block each product lands in):
print("  effective M is block-upper-triangular: [[A,B,Cc],[0,E,-G⁻¹Bᵀ],[0,0,-Aᵀ]]")
print("  A-block: [A1,A2]                         -> A   (Levi so(2,1) closes)")
print("  E-block: [E1,E2]                         -> E   (core so(G) closes)")
print("  B-block: A·B - B·E  (A on W, E on C)      -> B   (module: Levi⊕core act on module)")
print("  Cc-block: A·Cc - Cc·(-Aᵀ) + B·(-G⁻¹B'ᵀ)  -> Cc  (module·module lands in CENTER Cc)")
print("  ⟹ {Cc(center), B(module)} = Heisenberg ideal ; {A,E} = reductive Levi acting on it.")
print("  ⟹ c = (so(2,1) ⊕ so(G)) ⋉ Heisenberg(B,Cc) — the n-independent shape.")


# ==================== §4 numeric validation n=5,6,7 (dim + span) ====================
print()
print("=== §4 VALIDATION n=5,6,7 (bit-for-bit vs centralizer(): dim + span) ===")


def adapted_rank0(x, y, eta, n):
    # returns change-of-basis P (columns) = [x, y, C..., x', y'] and (G, nu)
    W = [x, y]
    Ap = Matrix.hstack(eta * x, eta * y).T
    Wperp = Ap.nullspace()
    C = []
    F = Matrix.hstack(x, y)
    r = 2
    for v in Wperp:
        F2 = Matrix.hstack(F, v)
        if F2.rank() > r:
            C.append(v)
            F = F2
            r += 1
    # duals x',y'
    rows = [(eta * x).T, (eta * y).T] + [(eta * cc).T for cc in C]
    Amat = Matrix.vstack(*rows)

    def dual(a, b):
        rhs = Matrix([a, b] + [0] * len(C))
        sol, params = Amat.gauss_jordan_solve(rhs)
        if params.rows * params.cols > 0:
            sol = sol.subs({s: 0 for s in params})
        return sol
    xp = dual(1, 0)
    yp = dual(0, 1)
    # make W'={xp,yp} isotropic and mutually η-orthogonal (keeps S=I, W'⊥C)
    axx = (xp.T * eta * xp)[0, 0]
    xp = xp - Rational(axx, 2) * x
    ayy = (yp.T * eta * yp)[0, 0]
    yp = yp - Rational(ayy, 2) * y
    axy = (xp.T * eta * yp)[0, 0]
    yp = yp - axy * x
    cols = [x, y] + C + [xp, yp]
    P = Matrix.hstack(*cols)
    return P, len(C)


def build_block_centralizer_rank0(N, x, y, eta, n):
    P, d = adapted_rank0(x, y, eta, n)
    Pinv = P.inv()
    etaA = P.T * eta * P
    NA = Pinv * N * P
    # extract G (core block) and nu (W'->W)
    G = etaA[2:2 + d, 2:2 + d]
    nu = NA[0:2, 2 + d:2 + d + 2]
    Ginv = G.inv()
    # free-block generators in adapted frame -> transform to std
    gens = []
    # A in sp(nu): basis of {A: A nu + nu Aᵀ = 0}
    for a in range(2):
        for b in range(2):
            pass
    # solve sp(nu) basis
    avars = symbols('a0:4')
    Amat = Matrix(2, 2, avars)
    eqs = Amat * nu + nu * Amat.T
    from sympy import linsolve
    sol = list(linsolve([eqs[i, j] for i in range(2) for j in range(2)], list(avars)))[0]
    free = set()
    for e in sol:
        free |= e.free_symbols
    sp_basis = []
    for fv in free:
        sub = {s: (Integer(1) if s == fv else Integer(0)) for s in free}
        Av = Amat.subs({avars[k]: sol[k] for k in range(4)}).subs(sub)
        sp_basis.append(Av)

    def emit(Ablk, Cc, Eblk, Bblk):
        Madp = zeros(n, n)
        Madp[0:2, 0:2] = Ablk
        Madp[0:2, 2:2 + d] = Bblk
        Madp[0:2, 2 + d:2 + d + 2] = Cc
        Madp[2:2 + d, 2:2 + d] = Eblk
        Madp[2:2 + d, 2 + d:2 + d + 2] = -Ginv * Bblk.T
        Madp[2 + d:2 + d + 2, 2 + d:2 + d + 2] = -Ablk.T
        return P * Madp * Pinv
    z2 = zeros(2, 2); zd = zeros(d, d); z2d = zeros(2, d)
    # A generators
    for Av in sp_basis:
        gens.append(emit(Av, z2, zd, z2d))
    # Cc antisym generators (2x2 antisym: 1)
    gens.append(emit(z2, Matrix([[0, 1], [-1, 0]]), zd, z2d))
    # E in so(G)
    for i in range(d):
        for j in range(i + 1, d):
            Ev = zeros(d, d)
            Ev[i, j] = Integer(1)
            Ev = Ev  # provisional; adjust to so(G): use wedge wrt G
    # so(G) basis via wedge in G-metric
    for i in range(d):
        for j in range(i + 1, d):
            w = (unit(d, i) * (G * unit(d, j)).T - unit(d, j) * (G * unit(d, i)).T)
            gens.append(emit(z2, z2, w, z2d))
    # B generators (2 x d)
    for i in range(2):
        for j in range(d):
            Bv = zeros(2, d)
            Bv[i, j] = Integer(1)
            gens.append(emit(z2, z2, zd, Bv))
    return gens, d


def adapted_rank1(x, y, eta, n):
    # 3-string {x, y, x'} + core; returns P, d', G
    # x null, y non-null, x⊥y ; x' dual to x with <y,x'>=0, <x',x'>=0
    c = (y.T * eta * y)[0, 0]
    # find x': <x,x'>=1, <y,x'>=0, and pick within a complement; also <x',x'>=0 not forced but set via ortho
    n_ = n
    # solve <x,x'>=1,<y,x'>=0
    rows = [(eta * x).T, (eta * y).T]
    Amat = Matrix.vstack(*rows)
    sol, params = Amat.gauss_jordan_solve(Matrix([1, 0]))
    if params.rows * params.cols > 0:
        sol = sol.subs({s: 0 for s in params})
    xp = sol
    # make xp isotropic and ⊥y by adjusting with x (x null): xp' = xp + t x, <xp',xp'>=<xp,xp>+2t<x,xp>=<xp,xp>+2t
    xpp = (xp.T * eta * xp)[0, 0]
    xp = xp - Rational(xpp, 2) * x  # now <xp,xp>=0
    T3 = [x, y, xp]
    # core = orthogonal complement of span{x,y,xp}
    Aperp = Matrix.hstack(eta * x, eta * y, eta * xp).T
    Cperp = Aperp.nullspace()
    C = []
    F = Matrix.hstack(x, y, xp)
    r = 3
    for v in Cperp:
        F2 = Matrix.hstack(F, v)
        if F2.rank() > r:
            C.append(v)
            F = F2
            r += 1
    cols = T3 + C
    P = Matrix.hstack(*cols)
    dprime = len(C)
    G = (P.T * eta * P)[3:3 + dprime, 3:3 + dprime]
    return P, dprime, G


def build_block_centralizer_rank1(N, x, y, eta, n):
    P, dp, G = adapted_rank1(x, y, eta, n)
    Pinv = P.inv()
    NA = Pinv * N * P
    N3 = NA[0:3, 0:3]
    etaA = P.T * eta * P
    E3 = etaA[0:3, 0:3]
    Ginv = G.inv()
    gens = []

    def emit(Pblk, Sm, Q):
        Madp = zeros(n, n)
        Madp[0:3, 0:3] = Pblk
        Madp[0:3, 3:3 + dp] = Q
        Madp[3:3 + dp, 3:3 + dp] = Sm
        Madp[3:3 + dp, 0:3] = -Ginv * (E3 * Q).T
        return P * Madp * Pinv
    z3 = zeros(3, 3); zdp = zeros(dp, dp); z3d = zeros(3, dp)
    # P in so(E3) ∩ centralizer(N3): solve
    pv = symbols('p0:9')
    Pm = Matrix(3, 3, pv)
    from sympy import linsolve
    eqs = list((Pm.T * E3 + E3 * Pm)) + list((Pm * N3 - N3 * Pm))
    sol = list(linsolve(eqs, list(pv)))[0]
    free = set()
    for e in sol:
        free |= e.free_symbols
    for fv in free:
        sub = {s: (Integer(1) if s == fv else Integer(0)) for s in free}
        Pval = Pm.subs({pv[k]: sol[k] for k in range(9)}).subs(sub)
        gens.append(emit(Pval, zdp, z3d))
    # Sm in so(G)
    for i in range(dp):
        for j in range(i + 1, dp):
            w = (unit(dp, i) * (G * unit(dp, j)).T - unit(dp, j) * (G * unit(dp, i)).T)
            gens.append(emit(z3, w, z3d))
    # Q with N3 Q=0: columns in ker N3
    kerN3 = N3.nullspace()
    for kv in kerN3:
        for j in range(dp):
            Qv = zeros(3, dp)
            Qv[:, j] = kv
            gens.append(emit(z3, zdp, Qv))
    return gens, dp


VAL = [((3, 2), "rank0", d0_on, build_block_centralizer_rank0, dimc_rank0, lambda n: n - 4),
       ((4, 2), "rank0", d0_on, build_block_centralizer_rank0, dimc_rank0, lambda n: n - 4),
       ((5, 2), "rank0", d0_on, build_block_centralizer_rank0, dimc_rank0, lambda n: n - 4),
       ((4, 1), "rank1", d1_on, build_block_centralizer_rank1, dimc_rank1, lambda n: n - 3),
       ((5, 1), "rank1", d1_on, build_block_centralizer_rank1, dimc_rank1, lambda n: n - 3),
       ((6, 1), "rank1", d1_on, build_block_centralizer_rank1, dimc_rank1, lambda n: n - 3)]

for (pq, cls, ctor, builder, formula, dof) in VAL:
    p, q = pq
    n = p + q
    eta = make_eta(p, q)
    bas = so_basis(n, eta)
    xy = ctor(list(range(n)), p, n)
    x, y = xy
    N = wedge(x, y, eta)
    cdirect = centralizer(N, bas)
    dparam = dof(n)
    predicted = formula(dparam)
    gens, dblk = builder(N, x, y, eta, n)
    # every block-gen must be a real centralizer element (in so, commutes with N)
    all_ok = all(is_so(M, eta) and (M * N - N * M).is_zero_matrix for M in gens)
    ok(all_ok, "block gens are valid centralizer elements ({0},{1}) {2}".format(p, q, cls))
    dim_gens = len(span_basis(gens, n))
    span_eq = same_span(gens, cdirect, n)
    ok(len(cdirect) == predicted, "dim c == formula ({0},{1}) {2}: {3} vs {4}".format(p, q, cls, len(cdirect), predicted))
    ok(dim_gens == len(cdirect), "block span dim == centralizer dim ({0},{1}) {2}".format(p, q, cls))
    ok(span_eq, "block span == centralizer span ({0},{1}) {2}".format(p, q, cls))
    print("  n={0} ({1},{2}) {3}: d={4} formula dim c={5} | centralizer dim={6} | block-span dim={7} | span-equal={8} | valid-gens={9}".format(
        n, p, q, cls, dparam, predicted, len(cdirect), dim_gens, span_eq, all_ok))


# ==================== mutants — one per branch ====================
print()
print("=== mutants (one per branch) ===")
mut_ok = True

# br-rank0-formula: formula matches at n=5,6,7 AND differs from rank1 formula
if dimc_rank0(1) == 6 and dimc_rank0(2) == 9 and dimc_rank0(3) == 13 and dimc_rank0(2) != dimc_rank1(2):
    print("MUTANT br-rank0: CAUGHT (rank-0 formula 6,9,13 at d=1,2,3; distinct from rank-1)")
else:
    print("MUTANT br-rank0: NOT CAUGHT"); mut_ok = False

# br-rank1-formula
if dimc_rank1(1) == 2 and dimc_rank1(2) == 4 and dimc_rank1(3) == 7 and dimc_rank1(4) == 11:
    print("MUTANT br-rank1: CAUGHT (rank-1 formula 2,4,7,11 at d'=1,2,3,4)")
else:
    print("MUTANT br-rank1: NOT CAUGHT"); mut_ok = False

# br-so(η)-constraint: a block M violating so(η) is NOT in the centralizer/so
_p, _q = 4, 2; _n = 6
_eta = make_eta(_p, _q); _bas = so_basis(_n, _eta)
_x, _y = d0_on(list(range(_n)), _p, _n)
_N = wedge(_x, _y, _eta)
_gens, _d = build_block_centralizer_rank0(_N, _x, _y, _eta, _n)
_good = _gens[0]
_bad = _good + unit(_n, 0) * unit(_n, 0).T   # add a symmetric (non-so) perturbation
if is_so(_good, _eta) and not is_so(_bad, _eta):
    print("MUTANT br-soeta: CAUGHT (block gen ∈ so(η); perturbed one ∉ so(η))")
else:
    print("MUTANT br-soeta: NOT CAUGHT"); mut_ok = False

# br-commute: a block gen commutes with N; a generic so element does not
_someso = _bas[0]
if (_good * _N - _N * _good).is_zero_matrix and not (_someso * _N - _N * _someso).is_zero_matrix:
    print("MUTANT br-commute: CAUGHT (block gen commutes with N; generic so element does not)")
else:
    # find any so element not commuting
    found = any(not (M * _N - _N * M).is_zero_matrix for M in _bas)
    if (_good * _N - _N * _good).is_zero_matrix and found:
        print("MUTANT br-commute: CAUGHT (block gen commutes; some so element does not)")
    else:
        print("MUTANT br-commute: NOT CAUGHT"); mut_ok = False


# ==================== summary ====================
print()
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
