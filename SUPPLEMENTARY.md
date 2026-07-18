# Preprint-2 — Supplementary material

*Centralizers of nilpotent wedges in real orthogonal Lie algebras so(p,q): a signature-resolved
Levi⋉radical map* — machine-verification package (lane-C, S987).

This accompanies `preprint2_en.tex` (§5 "Machine verification").  Everything below is **kernel-checked in
Lean 4 / mathlib v4.32.0**; the axiom audit is the standard triple `[propext, Classical.choice, Quot.sound]`
on every reported theorem — **no `sorry`, no `native_decide`** (the tactic is decidable `simp`/`norm_num`;
`native_decide` is deliberately avoided, being outside the trusted kernel via `Lean.ofReduceBool`).

## 1. Lean modules (source in `lean/VGLean/VGLean/`)

| module | object | what is kernel-checked |
|:--|:--|:--|
| `So21.lean` | **A1** — (2,2) rank-0 core | c(N) dim 4 = so(2,1)⊕ℝ; N nilpotent, basis ∈ so(η), [·,N]=0, full bracket table (16 thm) |
| `So51r1.lean` | **A2** — (5,1) rank-1 | c(N) = ℝ⊕(so(3)⋉ℝ³), dim 7; memberships, centralizer law, both bracket tables (iso), independence minor |
| `So42r1.lean` | **A2** — (4,2) rank-1 | c(N) = ℝ⊕(so(2,1)⋉ℝ³), dim 7 |
| `So33r1.lean` | **A2** — (3,3) rank-1 | c(N) = ℝ⊕(so(2,1)⋉ℝ³), dim 7 |
| `So32r0.lean` | **A2** — (3,2) rank-0 | c(N) = sp(2,ℝ)⋉h₃, dim 6 |
| `So42r0.lean` | **A2** — (4,2) rank-0 | c(N) = (sp(2,ℝ)⊕so(2))⋉h₅, dim 9; reductive centre **compact** (B8³=−B8) |
| `So33r0.lean` | **A2** — (3,3) rank-0 | c(N) = (sp(2,ℝ)⊕so(1,1))⋉h₅, dim 9; reductive centre **boost** (B8³=+B8) |

Per A2 file: `N` nilpotent · `N, Bᵢ ∈ so(η)` (skew-adjointness) · `[Bᵢ,N]=0` (centralizer law, ⟹ B ⊂ c(N)) ·
the Levi anchor `ψ(Lᵢ) ∈ so(η')/sp(J)` · a linear-independence minor (`minorB·minorBinv = 1`) · **both**
bracket tables (core and construct) with **identical** structure constants — that equality *is* the explicit
isomorphism c(N) ≅ construct (S946).  432 theorems across A2, build clean.

**Honest boundary (stated in each file).** Lean proves {the basis is linearly independent, lies in c(N),
and closes with the measured bracket tables}; that the basis is *all* of c(N) (dimension-completeness) is the
symbolic probe (S933), not Lean.

## 2. Data and generator

- `src/symbolic/S946_w33_leg2b_iso_export.json` — the 6 explicit core↔construct isomorphisms
  (exact rational matrices, P/Q alignment, ψ generators); the `sc(core)==sc(construct)` equality verified
  both ways.  Provenance: `src/symbolic/S946_w33_leg2b_bt_verify_iso_blind.py`.
- `lean/artifacts/gen_A2_iso.py` — the generator that emits the A2 `.lean` files from exact
  rational data (SymPy); every matrix identity is verified in Python before emission and re-verified
  in-kernel by Lean (the fourth layer).

## 3. Reproduce the verification

```
cd lean/VGLean
lake exe cache get          # mathlib oleans (pinned v4.32.0)
lake build VGLean.So21 VGLean.So51r1 VGLean.So42r1 VGLean.So33r1 \
           VGLean.So32r0 VGLean.So42r0 VGLean.So33r0
```
Axiom audit (must return the triple, no `sorryAx`/`ofReduceBool`), e.g.:
```
#print axioms VGLean.A2.So32r0.brC_3_4
#print axioms VGLean.A2.So42r0.B8_cube
```

## 4. Probes (in this repository, under `src/symbolic/`)

Each ships its reference output (`*_run.log`); a re-run is bit-identical (`python <probe>.py`).

- **T17** (§2, map of 4 classes): `S933_w33_leg1_centralizer_structure_blind.py` +
  `S935_w33_leg1b_perfect_core_identify_blind.py` + `S937_w33_leg1c_levi_radical_blind.py` +
  `S940_w33_leg1d_radical_pin_blind.py`.
- **T18** (§3, all-n form): `S952_w33_leg3b_block_symbolic_blind.py`.
- **S946** (explicit isomorphisms, the data behind the Lean A2 equalities):
  `S946_w33_leg2b_bt_verify_iso_blind.py` + `S946_w33_leg2b_iso_export.json`.

(The programme's internal registry and review record are not published; every qualifier is stated in the
text in full, and every number here has a probe in this repository.)

## 5. Bibliography

`preprint2.bib` (10 references, LaTeX-escaped diacritics; from the lit-gate map
`hub/prime/LIT_GATE_PREPRINT2_centralizer_map.md`).

---
*The `.tex` is not compiled in this environment (no TeX toolchain) — it is a claim until a PDF is built.
DOI and release date in `citation.yaml` are `TBD` placeholders finalized by the author on release (separate
Zenodo DOI series).  — lane-C (Sigma), S987.*
