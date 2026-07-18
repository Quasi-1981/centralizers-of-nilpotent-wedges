# -*- coding: utf-8 -*-
# DIM: na (structure table of centralizers of nilpotent and mixed elements in so(p,q); 0 handles — the probe postulates nothing).
#
# ============================================================================
# CARVE CHOICE (stamped BEFORE any counting — first question of the probe)
# ----------------------------------------------------------------------------
# The split of c into bracket-closed "parts" that get matched against the menu
# {gl(m,R), u(m), so(p0,q0), sp(2m,R)} is done by ONE fixed rule, chosen once
# and aloud:  *** INVARIANT-SUBSPACE decomposition ***.
#
#   The ambient R^{p+q} is cut into A-invariant, eta-orthogonal blocks — the
#   spectral blocks of the semisimple part S (real primary decomposition, S929
#   blocks_of). The bracket-closed parts of c are the IMAGES of c restricted to
#   each block, identified against the menu by span-equality + bt_verify.
#   For a pure nilpotent (S=0) the ambient is one block (whole space, sig=(p,q)),
#   so c(N) itself is the single part matched against the menu.
#
#   Why this class (not derived-series, not center): it reuses S929 verbatim
#   (bit-fence of identity on overlapping strata) and each part carries a
#   nondegenerate form, so the menu is well-posed. The derived series and the
#   center are reported as INDEPENDENT structural columns, NOT as the carving.
# ============================================================================

import sys
sys.stdout.reconfigure(encoding='utf-8')

import os
import itertools
from math import lcm as _ilcm

from sympy import Matrix, Integer, Rational, zeros, eye, diag, symbols, Poly, gcd, sqrt as ssqrt

X_ = symbols('x')

_LOGPATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "S933_w33_leg1_centralizer_structure_blind_run.log")
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


# ==================== exact linear-algebra primitives ====================
# (copied VERBATIM from S929_w32_factor_identification_blind.py — bit-fence
#  of identity: overlapping strata must reproduce S929 bit-for-bit)

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


def inter_dim(A, B, sq):
    ra = span_rank(A, sq)
    rb = span_rank(B, sq)
    ru = Matrix.hstack(stack_flats(A, sq), stack_flats(B, sq)).rank()
    return ra + rb - ru


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


def commutes_all(cb, A):
    return all((M * A - A * M).is_zero_matrix for M in cb)


def is_nilp(A):
    n = A.rows
    A2 = A * A
    if A2.is_zero_matrix:
        return True
    if A2.trace() != 0:
        return False
    return (A ** n).is_zero_matrix


def derived_and_closed(cb, sq):
    if not cb:
        return 0, True
    fc = stack_flats(cb, sq)
    rc = fc.rank()
    brs = []
    for a in range(len(cb)):
        for b in range(a + 1, len(cb)):
            brs.append(flat(cb[a] * cb[b] - cb[b] * cb[a]))
    if not brs:
        return 0, True
    fb = Matrix.hstack(*brs)
    dimcc = fb.rank()
    closed = (Matrix.hstack(fc, fb).rank() == rc)
    return dimcc, closed


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
    return Poly(X_ ** n, X_)  # unreachable by Cayley-Hamilton


def squarefree(mp):
    me = mp.as_expr()
    g = gcd(me, me.diff(X_))
    return Poly(g, X_).degree() == 0


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


def cong_diag(Gin):
    # returns (D, T) with T^T G T = D diagonal (exact congruence)
    A = Gin.copy()
    d = A.rows
    T = eye(d)
    for i in range(d):
        if A[i, i] == 0:
            js = None
            for j in range(i + 1, d):
                if A[j, j] != 0:
                    js = j
                    break
            if js is not None:
                A.col_swap(i, js)
                A.row_swap(i, js)
                T.col_swap(i, js)
            else:
                jn = None
                for j in range(i + 1, d):
                    if A[i, j] != 0:
                        jn = j
                        break
                if jn is None:
                    continue
                A[:, i] = A[:, i] + A[:, jn]
                A[i, :] = A[i, :] + A[jn, :]
                T[:, i] = T[:, i] + T[:, jn]
        piv = A[i, i]
        if piv == 0:
            continue
        for j in range(i + 1, d):
            if A[i, j] != 0:
                f = A[i, j] / piv
                A[:, j] = A[:, j] - f * A[:, i]
                A[j, :] = A[j, :] - f * A[i, :]
                T[:, j] = T[:, j] - f * T[:, i]
    return A, T


# ---------- coordinates / structure constants ----------

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
    # direct structure constants of L must equal those transported through the model table
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


def bt_str(L, sq):
    tab = sc_table(L, sq)
    if tab is None:
        return "bt=UNCLOSED"
    items = []
    for (i, j) in sorted(tab.keys()):
        c = tab[(i, j)]
        if any(v != 0 for v in c):
            items.append("({0},{1}):({2})".format(i, j, ",".join(str(v).replace(" ", "") for v in c)))
    return "bt=[" + ",".join(items) + "]"


# ---------- invariant block decomposition of S ----------

def evalmat(pl, S):
    n = S.rows
    M = zeros(n, n)
    for c in pl.all_coeffs():
        M = M * S + c * eye(n)
    return M


def dual_poly(f):
    return Poly(f.as_expr().subs(X_, -X_), X_).monic()


def poly_str(pl):
    return str(pl.as_expr()).replace(" ", "").replace("**", "^")


def blocks_of(S, eta, n, tag):
    mp = minpoly_poly(S)
    ok(squarefree(mp), "S diagonalizable over C (squarefree minpoly) " + tag)
    _c, facs = mp.factor_list()
    fl = []
    for (f, mult) in facs:
        ok(mult == 1, "factor multiplicity 1 " + tag)
        fm = Poly(f, X_).monic()
        ok(fm.degree() <= 2, "factor degree <= 2 " + tag)
        if fm.degree() == 2:
            ok(fm.discriminant() < 0, "quadratic factor irreducible over R " + tag)
        fl.append(fm)
    fl = sorted(fl, key=lambda t: (t.degree(), str(t.as_expr())))
    seen = set()
    recs = []
    for f in fl:
        key = str(f.as_expr())
        if key in seen:
            continue
        fd = dual_poly(f)
        kd = str(fd.as_expr())
        if kd == key:
            bp = f
            pair = None
            seen.add(key)
        else:
            ok(kd in [str(x.as_expr()) for x in fl], "dual factor present " + tag)
            bp = Poly(f.as_expr() * fd.as_expr(), X_).monic()
            pair = (f, fd)
            seen.add(key)
            seen.add(kd)
        B = evalmat(bp, S)
        K = (B ** n).nullspace()
        P = Matrix.hstack(*K)
        d = P.cols
        ok(P.rank() == d, "block basis full column rank " + tag)
        g = P.T * eta * P
        sig = cong_signature(g)
        ok(sig[2] == 0, "block Gram nondegenerate " + tag)
        ok(sig[0] + sig[1] + sig[2] == d, "block sig counts sum to dim " + tag)
        ok(sig[0] + sig[1] == g.rank(), "block sig pos+neg = rank " + tag)
        ptpinv = (P.T * P).inv()
        Ts = ptpinv * P.T * (S * P)
        ok((P * Ts - S * P).is_zero_matrix, "restriction of S exact " + tag)
        halves = None
        if pair is not None:
            h1 = evalmat(pair[0], S).nullspace()
            h2 = evalmat(pair[1], S).nullspace()
            C1 = []
            for u in h1:
                c = ptpinv * P.T * u
                if (P * c - u).is_zero_matrix:
                    C1.append(c)
            C2 = []
            for u in h2:
                c = ptpinv * P.T * u
                if (P * c - u).is_zero_matrix:
                    C2.append(c)
            if C1 and C2 and len(C1) == len(C2) and len(C1) + len(C2) == d:
                halves = (Matrix.hstack(*C1), Matrix.hstack(*C2))
        recs.append(dict(poly=bp, pstr=poly_str(bp), P=P, d=d, g=g,
                         sig=(sig[0], sig[1]), ptpinv=ptpinv, T=Ts, halves=halves))
    recs = sorted(recs, key=lambda r: (r["poly"].degree(), r["pstr"]))
    tot = sum(r["d"] for r in recs)
    ok(tot == n, "block dims sum to n " + tag)
    allP = Matrix.hstack(*[r["P"] for r in recs])
    ok(allP.rank() == n, "blocks span R^n " + tag)
    for i in range(len(recs)):
        for j in range(i + 1, len(recs)):
            ok(Matrix.hstack(recs[i]["P"], recs[j]["P"]).rank() == recs[i]["d"] + recs[j]["d"],
               "blocks pairwise zero intersection " + tag)
            ok((recs[i]["P"].T * eta * recs[j]["P"]).is_zero_matrix,
               "blocks pairwise eta-orthogonal " + tag)
    return recs


def preserves(M, P):
    return Matrix.hstack(P, M * P).rank() == P.rank()


def restrict(M, rec, tag):
    R = rec["ptpinv"] * rec["P"].T * (M * rec["P"])
    ok((rec["P"] * R - M * rec["P"]).is_zero_matrix, "restriction exact " + tag)
    return R


# ---------- model builders (full menu) ----------

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


def model_so_g(g):
    d = g.rows
    return model_from_constraints(d, [lambda E: E.T * g + g * E])


def model_u_g(g, J):
    d = g.rows
    return model_from_constraints(d, [lambda E: E.T * g + g * E,
                                      lambda E: E * J - J * E])


def model_sp_w(w):
    d = w.rows
    return model_from_constraints(d, [lambda E: E.T * w + w * E])


def hyp_form(m):
    H = zeros(2 * m, 2 * m)
    for i in range(m):
        H[i, m + i] = Integer(1)
        H[m + i, i] = Integer(1)
    return H


def gl_H_basis(m):
    out = []
    for a in range(m):
        for b in range(m):
            H = zeros(2 * m, 2 * m)
            H[a, b] = Integer(1)
            H[m + b, m + a] = Integer(-1)
            out.append(H)
    return out


def hyper_from_halves(Cp, Cm, g):
    m = Cp.cols
    if not (Cp.T * g * Cp).is_zero_matrix:
        return None
    if not (Cm.T * g * Cm).is_zero_matrix:
        return None
    B = Cp.T * g * Cm
    if B.det() == 0:
        return None
    Q = Matrix.hstack(Cp, Cm * B.inv())
    if not (Q.T * g * Q - hyp_form(m)).is_zero_matrix:
        return None
    return Q


def hyper_from_split(g):
    d = g.rows
    if d % 2 != 0:
        return None
    m = d // 2
    D, T = cong_diag(g)
    for i in range(d):
        for j in range(d):
            if i != j and D[i, j] != 0:
                return None
    pos = [i for i in range(d) if D[i, i] > 0]
    neg = [i for i in range(d) if D[i, i] < 0]
    if len(pos) != m or len(neg) != m:
        return None
    used = set()
    pairs = []
    for i in pos:
        found = None
        for j in neg:
            if j in used:
                continue
            t = ssqrt(-D[i, i] / D[j, j])
            if t.is_rational:
                found = (j, t)
                break
        if found is None:
            return None
        used.add(found[0])
        pairs.append((i, found[0], found[1]))
    xs = []
    ys = []
    for (i, j, t) in pairs:
        u = T[:, i]
        v = t * T[:, j]
        xs.append(u + v)
        ys.append((u - v) / (2 * D[i, i]))
    Q = Matrix.hstack(*(xs + ys))
    if not (Q.T * g * Q - hyp_form(m)).is_zero_matrix:
        return None
    return Q


def try_gl_model(rec):
    d = rec["d"]
    if d % 2 != 0:
        return None
    m = d // 2
    if rec["sig"] != (m, m):
        return None
    Q = None
    if rec["halves"] is not None:
        Q = hyper_from_halves(rec["halves"][0], rec["halves"][1], rec["g"])
    if Q is None:
        Q = hyper_from_split(rec["g"])
    if Q is None:
        return None
    Qi = Q.inv()
    return [Q * H * Qi for H in gl_H_basis(m)]


def try_u_model(rec):
    d = rec["d"]
    T2 = rec["T"] * rec["T"]
    s = T2[0, 0]
    if not (T2 - s * eye(d)).is_zero_matrix:
        return None
    if not (s < 0):
        return None
    a = ssqrt(-s)
    if not a.is_rational:
        return None
    J = rec["T"] / a
    if not (J * J + eye(d)).is_zero_matrix:
        return None
    return model_u_g(rec["g"], J)


def antisym_basis(d):
    out = []
    for i in range(d):
        for j in range(i + 1, d):
            A = zeros(d, d)
            A[i, j] = Integer(1)
            A[j, i] = Integer(-1)
            out.append(A)
    return out


def inv_antisym_forms(L, d):
    ab = antisym_basis(d)
    if not ab:
        return []
    if not L:
        return ab
    cols = []
    for A in ab:
        parts = [flat(Xm.T * A + A * Xm) for Xm in L]
        cols.append(Matrix.vstack(*parts))
    ns = Matrix.hstack(*cols).nullspace()
    out = []
    for v in ns:
        W = zeros(d, d)
        for k in range(len(ab)):
            if v[k, 0] != 0:
                W = W + v[k, 0] * ab[k]
        out.append(W)
    return out


def find_nondeg_w(Ws, d):
    for W in Ws:
        if W.rank() == d:
            return W
    kk = len(Ws)
    if kk >= 2 and kk <= 8:
        for cf in itertools.product((0, 1, 2), repeat=kk):
            if all(c == 0 for c in cf):
                continue
            W = zeros(d, d)
            for k in range(kk):
                if cf[k]:
                    W = W + Integer(cf[k]) * Ws[k]
            if W.rank() == d:
                return W
    return None


def try_sp_model(rec, L):
    d = rec["d"]
    Ws = inv_antisym_forms(L, d)
    w = find_nondeg_w(Ws, d)
    if w is None:
        return None
    return model_sp_w(w)


# ---------- identification against the full menu ----------

COUNTS = {"gl": 0, "u": 0, "so": 0, "sp": 0, "OTHER": 0, "sub-of": 0}


def identify(rec, L, tag):
    d = rec["d"]
    p0, q0 = rec["sig"]
    dimL = span_rank(L, d)
    _dcc, closed = derived_and_closed(L, d)
    ok(closed, "image bracket-closed " + tag)
    cand = []
    glm = try_gl_model(rec)
    if glm is not None:
        ok(span_rank(glm, d) == (d // 2) ** 2, "gl model dim " + tag)
        cand.append(("gl({0},R)".format(d // 2), glm))
    um = try_u_model(rec)
    if um is not None:
        ok(span_rank(um, d) == (d // 2) ** 2, "u model dim " + tag)
        cand.append(("u({0})".format(d // 2), um))
    som = model_so_g(rec["g"])
    ok(span_rank(som, d) == d * (d - 1) // 2, "so model dim " + tag)
    ok(contains(som, L, d), "image inside so(g) " + tag)
    cand.append(("so({0},{1})".format(p0, q0), som))
    spm = try_sp_model(rec, L)
    if spm is not None:
        ok(span_rank(spm, d) == (d // 2) * (d + 1), "sp model dim " + tag)
        cand.append(("sp({0},R)".format(d), spm))
    matches = []
    for (name, mo) in cand:
        if same_span(L, mo, d):
            matches.append((name, mo))
    if matches:
        for (name, mo) in matches:
            mob = span_basis(mo, d)
            tab = sc_table(mob, d)
            ok(bt_verify(L, mob, tab, d), "bracket table vs model " + name + " " + tag)
            COUNTS[name.split("(")[0]] += 1
        return "match=" + "&".join(nm for (nm, _m) in matches) + ":dim" + str(dimL)
    containers = []
    for idx, (name, mo) in enumerate(cand):
        if contains(mo, L, d):
            containers.append((span_rank(mo, d), idx, name))
    if containers:
        containers.sort()
        COUNTS["sub-of"] += 1
        return "sub-of=" + containers[0][2] + ":dim" + str(dimL) + ":" + bt_str(span_basis(L, d), d)
    COUNTS["OTHER"] += 1
    diags = ",".join(name + ":int" + str(inter_dim(L, mo, d)) for (name, mo) in cand)
    return "OTHER:dim" + str(dimL) + "(" + diags + ")"


def blocks_str(recs):
    return "[" + ",".join("({0},{1},({2},{3}))".format(r["pstr"], r["d"], r["sig"][0], r["sig"][1])
                          for r in recs) + "]"


# ==================== NEW W33 structure primitives ====================

def unflat(v, n):
    return Matrix(n, n, [v[i, 0] for i in range(n * n)])


def subspace_intersection(A, B, n):
    # exact intersection of two spans of n x n matrices, returned as a basis
    FA = stack_flats(A, n)
    FB = stack_flats(B, n)
    if FA.cols == 0 or FB.cols == 0:
        return []
    H = Matrix.hstack(FA, -FB)
    ns = H.nullspace()
    ka = FA.cols
    mats = []
    for v in ns:
        a = v[0:ka, 0]
        fvec = FA * a
        if not fvec.is_zero_matrix:
            mats.append(unflat(fvec, n))
    return span_basis(mats, n)


def bracket_basis(L, n):
    brs = []
    for a in range(len(L)):
        for b in range(a + 1, len(L)):
            brs.append(L[a] * L[b] - L[b] * L[a])
    return span_basis(brs, n)


def derived_series(L, n):
    # c ⊇ [c,c] ⊇ [[c,c],[c,c]] ⊇ ... dims to stabilization (perfect core or 0)
    cur = span_basis(L, n)
    dims = [len(cur)]
    while len(cur) > 0:
        nxt = bracket_basis(cur, n)
        if len(nxt) == len(cur):   # nxt ⊆ cur, equal dim ⟹ equal span ⟹ perfect: stop
            break
        dims.append(len(nxt))
        cur = nxt
    return dims


def center_of(cb, n):
    # {M ∈ span(cb) : [M, X] = 0 for all X ∈ cb}
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


def ker_profile(N, n):
    # dims of ker N^k, k = 1,2,... to nilpotency degree (Jordan filtration)
    prof = []
    P = N
    k = 1
    while True:
        dk = n - P.rank()
        prof.append(dk)
        if P.is_zero_matrix or dk == n or k >= n:
            break
        P = P * N
        k += 1
    return prof


# ---------- W33 per-stratum pipeline (S929 pipeline body + structure cols) ----

def w33_pipeline(A, S, p, q, eta, bas, tag):
    n = p + q
    ok(is_so(A, eta), "A in so " + tag)
    recs = blocks_of(S, eta, n, tag)
    cb = centralizer(A, bas)
    ok(all(is_so(M, eta) for M in cb), "c-basis in so " + tag)
    ok(commutes_all(cb, A), "c-basis commutes " + tag)
    dimcc, closed = derived_and_closed(cb, n)
    ok(closed, "c closed under bracket " + tag)
    viol = 0
    for M in cb:
        for r in recs:
            if not preserves(M, r["P"]):
                viol += 1
    pres = "ALL" if viol == 0 else "VIOL:" + str(viol)
    ok(viol == 0, "all c elements preserve all blocks " + tag)
    Rls = []
    for r in recs:
        Rls.append([restrict(M, r, tag) for M in cb])
    if cb:
        rho_cols = []
        for i in range(len(cb)):
            rho_cols.append(Matrix.vstack(*[flat(Rls[k][i]) for k in range(len(recs))]))
        ker_rho = len(cb) - Matrix.hstack(*rho_cols).rank()
    else:
        ker_rho = 0
    images = []
    sumdim = 0
    for k, r in enumerate(recs):
        L = span_basis(Rls[k], r["d"])
        sumdim += len(L)
        res = identify(r, L, tag + " f=" + r["pstr"])
        images.append(r["pstr"] + ":" + res)
    audit_ok = (len(cb) == sumdim + ker_rho)
    ok(audit_ok, "dimension audit " + tag)
    # ---- extra structure columns (independent of the carving) ----
    dser = derived_series(cb, n)
    zc = len(center_of(cb, n))
    return dict(blocks=blocks_str(recs), dimc=len(cb), dimcc=dimcc, pres=pres,
                ker_rho=ker_rho, images="[" + "; ".join(images) + "]",
                audit="OK" if audit_ok else "FAIL({0} vs {1}+{2})".format(len(cb), sumdim, ker_rho),
                dser=dser, zc=zc, cb=cb)


# ---------- wedge constructors (kernel-index carriers, S929 conventions) ----

def d0_on(K, p, n):
    # rank-0 Gram wedge: x,y both isotropic, mutually eta-orthogonal (needs 2 pos & 2 neg)
    Kp = [a for a in K if a < p]
    Km = [a for a in K if a >= p]
    if len(Kp) >= 2 and len(Km) >= 2:
        x = unit(n, Kp[0]) + unit(n, Km[0])
        y = unit(n, Kp[1]) + unit(n, Km[1])
        return x, y
    return None


def d1_on(K, p, n):
    # rank-1 Gram wedge: x isotropic, y non-isotropic, x eta-orthogonal to y (needs 1 pos, 1 neg, |K|>=3)
    Kp = [a for a in K if a < p]
    Km = [a for a in K if a >= p]
    if len(Kp) >= 1 and len(Km) >= 1 and len(K) >= 3:
        a, b = Kp[0], Km[0]
        rest = [c for c in K if c not in (a, b)]
        c = rest[0]
        return unit(n, a) + unit(n, b), unit(n, c)
    return None


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
        if s != 0:  # tr(X*X) != 0 => not nilpotent
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


def q_gram(cb):
    d = len(cb)
    G = zeros(d, d)
    for a in range(d):
        for b in range(a, d):
            t = (cb[a] * cb[b]).trace()
            G[a, b] = t
            G[b, a] = t
    return G


def sig_list():
    out = []
    for n in (4, 5, 6):
        for q in range(0, n // 2 + 1):
            p = n - q
            if p >= q:
                out.append((p, q))
    return out


ROWS_NILP = [0]
ROWS_MIXED = [0]


# ============================================================================
# PART 1 — pure nilpotent strata  N = x ∧ y  (S = 0, whole space is one block)
# ============================================================================
print("--- part 1: pure nilpotent  N = x wedge y  (S=0) ---")

for (p, q) in sig_list():
    n = p + q
    eta = make_eta(p, q)
    bas = so_basis(n, eta)
    ok(len(bas) == n * (n - 1) // 2, "basis size so({0},{1})".format(p, q))
    for (cls, ctor, gr) in (("rank0", d0_on, 0), ("rank1", d1_on, 1)):
        xy = ctor(list(range(n)), p, n)
        if xy is None:
            ROWS_NILP[0] += 1
            print("NILP SIG=({0},{1}) | class={2} | constructible=N (no totally-isotropic pair of required corank) | ker-prof=n/a | dimc=n/a".format(p, q, cls))
            continue
        x, y = xy
        N = wedge(x, y, eta)
        gG = gram2(x, y, eta)
        ok(gG.rank() == gr, "gram rank {0} matches class {1} ({2},{3})".format(gr, cls, p, q))
        ok(is_so(N, eta), "N in so ({0},{1}) {2}".format(p, q, cls))
        ok(is_nilp(N), "N nilpotent ({0},{1}) {2}".format(p, q, cls))
        ok(not N.is_zero_matrix, "N nonzero ({0},{1}) {2}".format(p, q, cls))
        kp = ker_profile(N, n)
        # sign-fence: -eta gives the SAME so-algebra (same defining equation);
        # x,y stay isotropic/orthogonal under -eta => everything must be bit-identical
        eta2 = -eta
        bas2 = so_basis(n, eta2)
        ok(is_so(N, eta2), "N in so under -eta ({0},{1}) {2}".format(p, q, cls))
        cb1 = centralizer(N, bas)
        cb2 = centralizer(N, bas2)
        ok(len(cb1) == len(cb2), "sign-fence dimc(eta)=dimc(-eta) ({0},{1}) {2}".format(p, q, cls))
        ok(derived_series(cb1, n) == derived_series(cb2, n), "sign-fence derived-series ({0},{1}) {2}".format(p, q, cls))
        ok(len(center_of(cb1, n)) == len(center_of(cb2, n)), "sign-fence center ({0},{1}) {2}".format(p, q, cls))
        r = w33_pipeline(N, zeros(n, n), p, q, eta, bas, "N-{0} ({1},{2})".format(cls, p, q))
        ROWS_NILP[0] += 1
        print("NILP SIG=({0},{1}) | class={2} | constructible=Y | ker-prof={3} | dimc={4} | dim[c,c]={5} | derived={6} | dimZ={7} | IMAGES={8} | audit={9}".format(
            p, q, cls, kp, r["dimc"], r["dimcc"], r["dser"], r["zc"], r["images"], r["audit"]))


# ============================================================================
# PART 2 — mixed  A = S + N, [S,N]=0  :  verify c(A) = c(S) ∩ c(N)
#          overlapping strata J1-J4 reproduced VERBATIM (bit-fence vs S929)
# ============================================================================
print("--- part 2: mixed  A = S + N,  c(A) = c(S) cap c(N) ---")

# bit-fence expected values captured from S929 run (dimc, dimcc, blocks)
FENCE = {
    "J1": (2, 0, "[(x^2-1,4,(2,2))]"),
    "J2": (5, 3, "[(x,4,(2,2)),(x^2+1,2,(2,0))]"),
    "J3": (3, 0, "[(x,4,(3,1)),(x^2+1,2,(2,0))]"),
    "J4": (5, 3, "[(x,4,(2,2)),(x^2-1,2,(1,1))]"),
}

JCASES = []

# J1: (2,2) S = two equal B, N from deterministic scan in span of c(S)
_p, _q = 2, 2
_n = 4
_eta = make_eta(_p, _q)
_bas = so_basis(_n, _eta)
_S = block_gen(_n, _eta, 0, 2, 1) + block_gen(_n, _eta, 1, 3, 1)
_cb = centralizer(_S, _bas)
_Xn = jordan_scan(_cb, q_gram(_cb), _n)
ok(_Xn is not None, "J1 scan finds nilpotent")
JCASES.append(("J1", _p, _q, _S, "B(0,2)x1,B(1,3)x1", _Xn, "scan"))

# J2: (4,2) S = single R on (0,1), N = D0 wedge on complement
_p, _q = 4, 2
_n = 6
_eta = make_eta(_p, _q)
_S = block_gen(_n, _eta, 0, 1, 1)
_K = [2, 3, 4, 5]
_x, _y = d0_on(_K, _p, _n)
ok(gram2(_x, _y, _eta).is_zero_matrix, "J2 Gram rank 0")
JCASES.append(("J2", _p, _q, _S, "R+(0,1)x1", wedge(_x, _y, _eta), "D0"))

# J3: (5,1) S = single R on (0,1), N = D1 wedge on complement
_p, _q = 5, 1
_n = 6
_eta = make_eta(_p, _q)
_S = block_gen(_n, _eta, 0, 1, 1)
_K = [2, 3, 4, 5]
_x, _y = d1_on(_K, _p, _n)
ok(gram2(_x, _y, _eta).rank() == 1, "J3 Gram rank 1")
JCASES.append(("J3", _p, _q, _S, "R+(0,1)x1", wedge(_x, _y, _eta), "D1"))

# J4: (3,3) S = single B on (0,3), N = D0 wedge on complement
_p, _q = 3, 3
_n = 6
_eta = make_eta(_p, _q)
_S = block_gen(_n, _eta, 0, _p, 1)
_K = [1, 2, 4, 5]
_x, _y = d0_on(_K, _p, _n)
ok(gram2(_x, _y, _eta).is_zero_matrix, "J4 Gram rank 0")
JCASES.append(("J4", _p, _q, _S, "B(0,3)x1", wedge(_x, _y, _eta), "D0"))

for (jid, p, q, S, sstr, N, ncls) in JCASES:
    n = p + q
    eta = make_eta(p, q)
    bas = so_basis(n, eta)
    tag = jid + " (" + str(p) + "," + str(q) + ")"
    ok(is_so(N, eta), "N in so " + tag)
    ok(is_nilp(N), "N nilpotent " + tag)
    ok(not N.is_zero_matrix, "N nonzero " + tag)
    ok((S * N - N * S).is_zero_matrix, "[S,N]=0 " + tag)
    # Jordan preconditions: S semisimple (diagonalizable over C), N nilpotent, [S,N]=0
    ok(squarefree(minpoly_poly(S)), "S semisimple " + tag)
    A = S + N
    r = w33_pipeline(A, S, p, q, eta, bas, tag)
    # bit-fence vs S929
    exp_dc, exp_dcc, exp_bl = FENCE[jid]
    ok(r["dimc"] == exp_dc, "bit-fence dimc " + tag)
    ok(r["dimcc"] == exp_dcc, "bit-fence dimcc " + tag)
    ok(r["blocks"] == exp_bl, "bit-fence blocks " + tag)
    bit = "OK" if (r["dimc"] == exp_dc and r["dimcc"] == exp_dcc and r["blocks"] == exp_bl) else "FAIL"
    # centralizer identity  c(A) = c(S) cap c(N)  as SPANS (subspace equality)
    cS = centralizer(S, bas)
    cN = centralizer(N, bas)
    cA = r["cb"]
    inter = subspace_intersection(cS, cN, n)
    eq_span = same_span(cA, inter, n)
    ok(eq_span, "c(A) = c(S) cap c(N) span-equal " + tag)
    # cross-checks on the same fact
    ok(contains(cS, cA, n), "c(A) subset c(S) " + tag)
    ok(contains(cN, cA, n), "c(A) subset c(N) " + tag)
    ok(len(inter) == inter_dim(cS, cN, n), "intersection basis dim matches inter_dim " + tag)
    verdict = "EQUAL" if eq_span else "FAIL"
    ROWS_MIXED[0] += 1
    print("MIXED SIG=({0},{1}) | {2}[S={3};N={4}] | dimc={5} | dim[c,c]={6} | derived={7} | dimZ={8} | c(A)=c(S)cap c(N):{9} (dimcS={10},dimcN={11},dimInt={12}) | bit-fence={13} | IMAGES={14} | audit={15}".format(
        p, q, jid, sstr, ncls, r["dimc"], r["dimcc"], r["dser"], r["zc"], verdict,
        len(cS), len(cN), len(inter), bit, r["images"], r["audit"]))


# ============================================================================
# MUTANTS — each exercises a REAL new code path and must be CAUGHT
# ============================================================================
print("--- mutants ---")
mut_ok = True

# mu1: subspace_intersection / same_span path.
# Truth: for J2, c(A) = c(S) cap c(N).  Corruption: intersect c(S) with c(S)
# (i.e. pretend N contributes nothing) -> must NOT equal c(A) since c(A) ⊊ c(S).
_p, _q = 4, 2
_n = 6
_eta = make_eta(_p, _q)
_bas = so_basis(_n, _eta)
_S = block_gen(_n, _eta, 0, 1, 1)
_x, _y = d0_on([2, 3, 4, 5], _p, _n)
_N = wedge(_x, _y, _eta)
_A = _S + _N
_cA = centralizer(_A, _bas)
_cS = centralizer(_S, _bas)
_cN = centralizer(_N, _bas)
ok(same_span(_cA, subspace_intersection(_cS, _cN, _n), _n), "mu1 baseline: true intersection equals c(A)")
if not same_span(_cA, subspace_intersection(_cS, _cS, _n), _n):
    print("MUTANT mu1: CAUGHT (c(S) cap c(S) != c(A): dim {0} vs {1})".format(len(_cS), len(_cA)))
else:
    print("MUTANT mu1: NOT CAUGHT")
    mut_ok = False

# mu2: derived_series path.
# Hand-built solvable aff(1) = <H,E>, [H,E]=2E  -> series must reach 0: [2,1,0].
# Hand-built perfect so(2,1) -> series stabilizes nonzero: [3].
_H = Matrix([[Integer(1), 0], [0, Integer(-1)]])
_E = Matrix([[0, Integer(1)], [0, 0]])
_ds_solv = derived_series([_H, _E], 2)
_so21 = so_basis(3, make_eta(2, 1))
_ds_perf = derived_series(_so21, 3)
ok(_ds_solv == [2, 1, 0], "mu2 baseline: solvable aff(1) derived series [2,1,0]")
ok(_ds_perf == [3], "mu2 baseline: perfect so(2,1) derived series [3]")
if _ds_solv[-1] == 0 and _ds_perf[-1] != 0 and _ds_solv != _ds_perf:
    print("MUTANT mu2: CAUGHT (derived series separates solvable {0} from perfect {1})".format(_ds_solv, _ds_perf))
else:
    print("MUTANT mu2: NOT CAUGHT")
    mut_ok = False

# mu3: center_of path.
# so(2,1) is simple -> center 0.  Abelian <J> (single generator) -> center 1.
# Inject a non-commuting element into the abelian set: center must NOT grow to 2.
_ctr_simple = len(center_of(_so21, 3))
_J = Matrix([[0, Integer(-1)], [Integer(1), 0]])
_ctr_ab = len(center_of([_J], 2))
_tampered = [_J, _E]        # [J,E] != 0, so E is not central; center stays span{J}? check
_ctr_tamp = len(center_of(_tampered, 2))
ok(_ctr_simple == 0, "mu3 baseline: center(so(2,1)) = 0")
ok(_ctr_ab == 1, "mu3 baseline: center(abelian <J>) = 1")
if _ctr_simple == 0 and not (_J * _E - _E * _J).is_zero_matrix and _ctr_tamp < 2:
    print("MUTANT mu3: CAUGHT (center rejects non-commuting injection: dimZ={0}<2)".format(_ctr_tamp))
else:
    print("MUTANT mu3: NOT CAUGHT")
    mut_ok = False

# mu4: ker_profile path.
# rank-0 wedge -> N^2=0 : profile [n-2, n].  rank-1 wedge -> N^3=0 : profile [n-2, n-1, n].
_e6 = make_eta(4, 2)
_x0, _y0 = d0_on([0, 1, 4, 5], 4, 6)
_N0 = wedge(_x0, _y0, _e6)
_x1, _y1 = d1_on([0, 4, 1], 4, 6)
_N1 = wedge(_x1, _y1, _e6)
_kp0 = ker_profile(_N0, 6)
_kp1 = ker_profile(_N1, 6)
ok(_kp0 == [4, 6], "mu4 baseline: rank-0 wedge profile [4,6]")
ok(_kp1 == [4, 5, 6], "mu4 baseline: rank-1 wedge profile [4,5,6]")
if len(_kp0) == 2 and len(_kp1) == 3 and _kp0 != _kp1:
    print("MUTANT mu4: CAUGHT (ker-profile separates rank-0 {0} from rank-1 {1})".format(_kp0, _kp1))
else:
    print("MUTANT mu4: NOT CAUGHT")
    mut_ok = False

# mu5: menu bracket-table path (reused identify).  Corrupt one structure constant
# of a computed model table -> bt_verify must report MISMATCH.
_g3 = eye(3)
_mod3 = span_basis(model_so_g(_g3), 3)
_tab3 = sc_table(_mod3, 3)
ok(_tab3 is not None, "mu5 baseline: model table exists")
ok(bt_verify(_mod3, _mod3, _tab3, 3), "mu5 baseline: uncorrupted table verifies")
_tab_bad = dict(_tab3)
_k0 = sorted(_tab_bad.keys())[0]
_row = list(_tab_bad[_k0])
_row[0] = _row[0] + 1
_tab_bad[_k0] = tuple(_row)
if not bt_verify(_mod3, _mod3, _tab_bad, 3):
    print("MUTANT mu5: CAUGHT (bracket-table MISMATCH reported)")
else:
    print("MUTANT mu5: NOT CAUGHT")
    mut_ok = False


# ============================================================================
# summary
# ============================================================================
print("SUMMARY: rows_nilp={0} | rows_mixed={1}".format(ROWS_NILP[0], ROWS_MIXED[0]))
print("SUMMARY: matches gl={0} | u={1} | so={2} | sp={3} | OTHER={4} | sub-of={5}".format(
    COUNTS["gl"], COUNTS["u"], COUNTS["so"], COUNTS["sp"], COUNTS["OTHER"], COUNTS["sub-of"]))
print("SUMMARY: asserts_passed={0} | FAIL={1}".format(ASSERT_PASS[0], FAILS[0]))

# ---------- self-scan of source and produced log text for banned substrings ----------

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
