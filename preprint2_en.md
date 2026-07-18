## Abstract

For a rank-2 nilpotent (a wedge N = x∧y) in a real orthogonal Lie algebra so(p,q), the centralizer c(N)
decomposes as a reductive part in semidirect product with a nilradical — a framework classical over
algebraically closed fields (Springer–Steinberg; Collingwood–McGovern). We give the *signature-resolved*
so(p,q) form of this decomposition for the *enumerated* signatures n = p+q ≤ 6: the non-abelian part is
exhausted by four classes, each a 3-dimensional engine in semidirect product with a nilpotent module,
falling into a dichotomy between the affine type so(p′,q′)⋉ℝ^{d′} and the Jacobi type sp(2m,ℝ)⋉h_{2m+1}.
The governing mechanism is obtained for all n in block-symbolic form (by solving [M,N] = 0, not by fitting).
A signature biconditional — *for the soft (rank-1) family*, the reductive Levi is compact iff q = 1 —
follows from the definiteness of (p−2, q−1). The explicit isomorphisms are machine-verified (Lean/mathlib,
kernel-checked; axioms [propext, Classical.choice, Quot.sound], no native_decide). Three statements — the
signature-resolved dichotomy table, the all-n centralizer form, and the soft-family compact-Levi
biconditional — are absent from the literature surveyed (the nearest, Đoković–Lemire–Sekiguchi 2001, gives
the closure order, not centralizer structure). No physical reading of any object is made or implied.

---

## §1. Setup and framework

Let (V, η) be a real quadratic space of signature (p, q), n = p + q, and so(p, q) its orthogonal Lie
algebra. A *wedge* N = x∧y (rank-2 nilpotent, x, y isotropic and mutually orthogonal representatives)
generates a nilpotent adjoint orbit; we study its centralizer c(N) = {A ∈ so(p,q) : [A, N] = 0}.

Over an algebraically closed field the structure c(N) = (reductive) ⋉ (unipotent radical) is classical
(Springer–Steinberg 1970; Collingwood–McGovern, Thm 6.1.3), with reductive parts tabulated by partition
for the complex classical algebras. Our contribution is the *real, signature-resolved* form: how the
Levi⋉radical splits as a function of (p, q). The nearest classical real work, Đoković–Lemire–Sekiguchi
2001, classifies O(p,q)-orbits and their closure order (min(p,q) ≤ 7) but not the centralizer structure —
so the table below sits in a documented gap. (Explicit real centralizers are available for the exceptional
algebras — Đoković 1988 — and Levi decompositions of nilpotent centralizers in classical groups are known
over algebraically closed fields — Babinski–Stewart 2016 — but neither yields a signature-resolved so(p,q)
table.)

**Scope (load-bearing qualifiers).** All statements are for wedge nilpotents (rank N = 2); higher Jordan
types are a named tail, out of scope. Strata are given by coordinate representatives; the invariants are
representation-independent (checked on independent representatives of each class). The classical frames
invoked — Levi–Malcev decomposition, sl(2)-module theory, the classification of Heisenberg algebras — are
cited, not re-derived (multiplicity 0). Named objects that appear (Poincaré 2+1 = iso(2,1), Euclidean
e(3), oscillator/Jacobi = so(2,1)⋉h₃) are *flags* — they emerged by measurement on degeneracy strata,
not by assumption.

## §2. The signature-resolved centralizer map

**Theorem (centralizer map, enumerated signatures n ≤ 6).** The non-abelian part of c(N) for a wedge N in
so(p,q) is exhausted by four classes, each a 3-dimensional engine in semidirect product with a nilpotent
module:

- **(i)** bare so(2,1) — deep kernels ker = 2, mixed J2/J4;
- **(ii)** Levi ⋉ ℝ³ (irreducible 3): e(3) iff q = 1, iso(2,1) iff q ≥ 2 — soft kernels ker = 4;
- **(iii)** so(2,1) ⋉ h₃, with rad/Z the fundamental-2 (weights ±1) — deep (3,2);
- **(iv)** so(2,1) ⋉ h₅, with rad/Z of type 2+2 (weights {+1,+1,−1,−1}, commutant-dim 4, min-cyclic 2;
  *not* the irreducible spin-3/2) — deep n = 6.

The solvable branch (no Levi factor) gives (4,1)r1 ⊥ (3,2)r1 as *distinct* algebras (the discriminant-form
signature of ad on [L,L]: rotation ±i elliptic ⊥ boost ±1 hyperbolic). The abelian case: soft ker = 2, and
(3,1) entirely (the centre is the whole centralizer).

**Radical dichotomy (measured, no interpretation).** Soft kernels carry an *abelian* (translational)
radical; deep kernels carry a *Heisenberg* radical (h₃/h₅, canonical pairs in rad/Z, weights ±1). Two
species: translational ⊥ symplectic.

**Load-bearing qualifiers.** This is an *enumeration of signatures n ≤ 6*, not an arbitrary-n theorem (the
mechanism derivation for all n is the named tail, closed at §3). "Engine compactness ⟺ q = 1" holds *within
the enumeration*. The classification is by structural invariants over the enumerated signatures; matching
invariants are not claimed to pin the isomorphism class beyond the cases exhibited.

*Address:* probes S933, S935, S937, S940 (`src/symbolic/`, each with its reference log).
*Citation anchor:* reductive⋉nilradical — Springer–Steinberg 1970, CM 6.1.3; the real so(p,q) table is the
white spot (nearest, DLS 2001, gives closures, not structure).

---

## §3. The all-n centralizer form

**Theorem (centralizer form, all n).** The mechanism is derived for all n — not enumerated — by solving
[M, N] = 0 in block-symbolic form (a matrix symbol with symbolic kernel dimension d); the resulting form
is n-independent, obtained by *solving* the equations so(η) ∧ [M, N] = 0, not by fitting. In two families:

- **rank-0:** c(N) ≅ (sp(2,ℝ) ⊕ so(η|G)) ⋉ h_{2d+1}, with d = n − 4 and η|G of signature (p−2, q−2); the
  module is F₂ ⊗ V_d, and *the centre is born from [module, module]* — the Heisenberg structure is not
  postulated, it falls out. dim c(N) = d(d−1)/2 + 2d + 4.
- **rank-1:** c(N) ≅ ℝ ⊕ (so(η|G′) ⋉ ℝ^{d′}), with d′ = n − 3 and η|G′ of signature (p−2, q−1);
  dim c(N) = d′(d′+1)/2 + 1. Here *the Levi is compact iff q = 1* is now a **theorem** (definiteness of
  (p−2, q−1) holds iff q = 1), not an empirical observation.

**Load-bearing qualifiers.** Only *wedge* nilpotents (rank N = 2; higher Jordan types are a named tail).
The derivation is machine-symbolic (block_collapse) plus instance validation on n = 5–7 by span-equality
(6/6) plus the closed form checked against all 15 measured centralizer dimensions (8/8 dimension classes),
with the n = 8 control independently reproducing the rank-0 closed form at d = 4 (dim 18, h₉, Levi
so(2,1) ⊕ so(2,2); Lane-B visa J-0444); the orbit representative of a wedge is the Witt representative
(cited, multiplicity 0). *A Lean-level formal
proof is the endgame, not this act:* the free/linked/zero split of the block decomposition is *read* from
the symbolic equations, not auto-solved end-to-end — the guard is the span-equality instance check on
n = 5–7 (Lane-B visa J-0423).

*Address:* probe S952 (`src/symbolic/`, with its reference log). *Citation anchor:* the all-n centralizer form
for so(p,q) nilpotents is a white spot; its components (Levi decomposition, sl(2)-modules, the Heisenberg
parabolic — Jia, arXiv:2501.12406) are cited.

## §4. The bridge: "construct = output"

For each core we *exhibit* an explicit two-sided isomorphism (bt_verify) between the centralizer core and
the construct, given by explicit P/Q-aligned rational matrices (S946) — we do **not** appeal to an
existence theorem (Levi–Malcev). Presenting the isomorphism, rather than invoking its existence, is exactly
the machine-verifiable form used in §5.

*Address:* src/symbolic/S946_w33_leg2b_iso_export.json (6 isomorphisms, n = 5, 6);
S946_w33_leg2b_bt_verify_iso_blind.py.

## §5. Machine verification

The explicit isomorphisms are verified in Lean 4 / mathlib (v4.32.0), as a fourth layer over the symbolic
probes.

- **A1** — the (2,2) rank-0 core: centralizer of dimension 4 = so(2,1) ⊕ ℝ (centre); 16 theorems
  kernel-checked (So21.lean).
- **A2 — the full centralizer c(N), 6/6** (the ℝ-centre for rank-1 and the reductive centre for rank-0 are
  included): So51r1 · So42r1 · So33r1 (rank-1, full dim 7 = core ⊕ ℝ) and So32r0 · So42r0 · So33r0
  (rank-0; the deep n=6 cases dim 9 = (sp(2,ℝ) ⊕ so(η|G)) ⋉ h₅, the (3,2) case dim 6). 432 theorems,
  build clean.

**Axiom audit.** `#print axioms` returns [propext, Classical.choice, Quot.sound] on every reported theorem —
with **no** `sorry` and **no** `native_decide` (the tactic is decidable `simp`/`norm_num`; `native_decide`
is deliberately avoided, being outside the trusted kernel via `Lean.ofReduceBool`).

**Honest boundary.** Lean proves {the basis is linearly independent, lies in c(N), and closes with the
measured bracket tables}; that the basis is *all* of c(N) (dimension-completeness) is the symbolic probe
(S933), not Lean.

**Signature instance of the reductive centre so(η|G) = so(p−2, q−2).** For the deep n=6 rank-0 cores the
reductive centre is the compact so(2) or the non-compact boost so(1,1) according to the signature: So42r0
(4,2) → the extra generator W satisfies W³ = −W (minimal polynomial x(x²+1), eigenvalues ±i) → **compact
so(2)** ((2,0) definite); So33r0 (3,3) → W³ = +W (x(x²−1), eigenvalues ±1) → **boost so(1,1)** ((1,1)
indefinite) — at an *identical* core mechanism sp(2,ℝ) ⋉ h₅. Both `W ∈ so(η)` and the eigenvalue-type
invariant `W³ = ∓W` are named and kernel-checked (theorems `B8_inSO`, `B8_cube`). (Note: W² is *not* ±1 on
the full space — only on its 2-plane; the clean full-matrix invariant of the eigenvalue type is W³ = ∓W.)

*Address:* Lean project in `lean/VGLean/`; data `lean/artifacts/gen_A2_iso.py`, `src/symbolic/S946_w33_leg2b_iso_export.json`.
*Strongest card:* machine verification renders our explicit real centralizers irrefutable — the literature
gives the framework; we give verified instances in the white spot.

## §6. Positioning: three documented gaps

The novelty rests on three statements absent from the literature we surveyed, each standing on a cited
scaffold:

1. **A real so(p,q) Levi⋉radical table** (signature-resolved) — a gap; the nearest, Đoković–Lemire–Sekiguchi
   2001, gives the closure order, not the structure.

2. **The affine ⟺ Jacobi dichotomy** classifying wedge centralizers for n ≤ 6 — a gap (a new packaging; the
   components — Eichler–Zagier; Berndt–Schmidt; Berceanu (explicit sp⋉Heisenberg commutators) — are cited).

3. **The "compact-Levi ⟺ q = 1" biconditional** — not written down anywhere as a theorem. It is *reinforced
   by machine instances* (§5): kernel-checked on both sides at an identical core — So42r0 compact so(2) ⊥
   So33r0 boost so(1,1). We state "verified instances in a white spot," **not** "an ∀-theorem
   kernel-checked" (the ∀-biconditional is proved from signed-tableau definiteness — signed Young diagrams,
   Neuttiens–Pierard de Maujouy 2026; Lean supplies instances).

**Reviewer risk.** "The components are known" → the components, yes; but the dichotomy-as-classification for
so(p,q) n ≤ 6 and the signature biconditional are not written down; DLS 2001 does closures, not structure.

**Card formulation (no over-claim).** "The first explicit real **machine-verified instances** of the
signature splitting of the reductive centre so(η|G) = so(p−2, q−2); the general form is *enumerative*." This
holds the boundary: the instances are kernel-checked ⊥ the general ∀-biconditional is signed-tableau (not to
be re-claimed as "a theorem kernel-checked").

## References

1. D. H. Collingwood, W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van Nostrand Reinhold, 1993.

2. T. A. Springer, R. Steinberg, "Conjugacy classes," LNM **131**, Springer, 1970, pp. 167–266.

3. D. Ž. Đoković, N. Lemire, J. Sekiguchi, *Tohoku Math. J.* **53**(3) (2001) 395–442, DOI 10.2748/tmj/1178207418.

4. D. Ž. Đoković, *J. Algebra* **112** (1988) 503–524; **116** (1988) 196–207.

5. A. P. Babinski, D. I. Stewart, arXiv:1611.00937 (2016); *J. Pure Appl. Algebra*.

6. M. Eichler, D. Zagier, *The Theory of Jacobi Forms*, Progr. Math. **55**, Birkhäuser, 1985.

7. R. Berndt, R. Schmidt, *Elements of the Representation Theory of the Jacobi Group*, Progr. Math. **163**, Birkhäuser, 1998.

8. S. Berceanu, arXiv:math/0604381; arXiv:1903.10721.

9. G. Neuttiens, J. Pierard de Maujouy, arXiv:2604.01427 (2026).

10. B. Jia, "Minimal Nilpotent Orbits of type D and E," arXiv:2501.12406.

---

*Provenance (§0, per preprint-1):* no result depends on a physical reading of any object, nor asserts one.
