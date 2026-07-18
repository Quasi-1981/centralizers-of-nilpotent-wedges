# Centralizers of nilpotent wedges in real orthogonal Lie algebras so(p,q): a signature-resolved Levi⋉radical map

*(programme "Geometry of the vacuum", floor −1)*

A work of pure mathematics about the centralizers of rank-2 nilpotents in the
real orthogonal Lie algebras `so(p,q)`. It asks a single structural question — how
does the centralizer of a wedge split, as a function of the signature `(p,q)` — and
answers it with an explicit, machine-checkable map.

Everything below is checkable from this repository alone. Nothing here asks you to
trust a file you cannot open.

---

## What is defined

`so(p,q)` is the real orthogonal Lie algebra of a quadratic space of signature
`(p,q)`, `n = p+q`. A **wedge** is a rank-2 nilpotent `N = x∧y` built from two
isotropic, mutually orthogonal vectors; it generates a nilpotent adjoint orbit. Its
**centralizer** is `c(N) = { A ∈ so(p,q) : [A,N] = 0 }`.

Over an algebraically closed field the shape `c(N) = (reductive) ⋉ (nilradical)` is
classical (Springer–Steinberg 1970; Collingwood–McGovern). What is measured here is
the **real, signature-resolved** form: how that Levi⋉radical splits with `(p,q)`.

## What is proved

- **A signature-resolved centralizer map** (enumerated signatures `n ≤ 6`). The
  non-abelian part is exhausted by four classes, each a 3-dimensional engine in
  semidirect product with a nilpotent module, falling into a dichotomy between the
  **affine** type `so(p′,q′)⋉ℝ^{d′}` and the **Jacobi** type `sp(2m,ℝ)⋉h_{2m+1}`.
  *(§2 · registry T17 · probes `S933`–`S940`)*
- **The all-`n` centralizer form.** The governing mechanism is obtained *for all n*
  in block-symbolic form — by solving `[M,N] = 0`, not by fitting. In the rank-0
  family the Heisenberg centre is *born from* `[module, module]`; it is not
  postulated. *(§3 · registry T18 · probe `S952`)*
- **A signature biconditional.** For the soft (rank-1) family, the reductive Levi is
  compact **iff** `q = 1` — a definiteness condition on `(p−2, q−1)`.
  *(§3 · registry T18)*

Each statement carries its limits as part of it (§2–§3). Three of them — the
signature-resolved dichotomy table, the all-`n` form, and the soft-family
compact-Levi biconditional — are **absent from the literature surveyed**; the
nearest classical real work (Đoković–Lemire–Sekiguchi 2001) gives the closure order
of the orbits, not the structure of the centralizer.

## Scope — declared, not argued

- **Wedge nilpotents only** (rank `N = 2`); higher Jordan types are a named tail,
  out of scope.
- The signature-resolved map is an **enumeration of signatures `n ≤ 6`**, not a
  theorem for all `n`; the all-`n` *mechanism* is derived symbolically, its
  instance-validation runs on `n = 5–8`.
- Classical frames — Levi–Malcev decomposition, `sl(2)`-module theory, the
  classification of Heisenberg algebras — are **cited, not re-derived**.
- **No physical reading of any object** — the words that would carry one have no
  definition at this level. That is scope, not oversight.

## Machine verification (supplementary)

The explicit isomorphisms behind the map are verified in **Lean 4 / mathlib**
(`v4.32.0`), as a fourth layer over the symbolic probes — see `SUPPLEMENTARY.md`.
Every reported theorem depends only on the axioms `propext`, `Classical.choice`,
`Quot.sound`, with **no `sorry` and no `native_decide`** (the trusted-kernel path
only). The honest boundary is stated where it bites: Lean proves the basis is
independent, lies in `c(N)`, and closes with the measured bracket tables; that the
basis is *all* of `c(N)` (dimension-completeness) is the symbolic probe, not Lean.

## How to read

`preprint2_en.tex` (and the built `preprint2_en.pdf`) is the full text.
`preprint2.bib` is its bibliography. `SUPPLEMENTARY.md` describes the machine
verification and how to reproduce it.

## What is in here

| path | what |
|---|---|
| `preprint2_en.tex` / `.pdf` | the full text: the map, the all-`n` form, the biconditional, limits |
| `preprint2_en.md` | the same text in Markdown (the generator's source) |
| `preprint2.bib` | bibliography |
| `SUPPLEMENTARY.md` | the Lean/mathlib verification: objects, what is proved, how to reproduce |
| `citation.yaml` | single source of the publication metadata |
| `.zenodo.json` / `CITATION.cff` | generated from `citation.yaml` — do not edit by hand |
| `src/symbolic/` | the probes behind T17 / T18 and the explicit isomorphisms, each with its reference log |
| `lean/VGLean/` | the Lean 4 / mathlib project — the kernel-checked verification (build with `lake exe cache get && lake build`) |
| `lean/artifacts/gen_A2_iso.py` | generator emitting the A2 `.lean` files from exact rational data |

The working acts of the programme (the internal registry and review record) are
**not published**, and nothing here rests on them: every qualifier is stated in the
text in full, and every number has a probe **in this repository** (see `SUPPLEMENTARY.md`).

## Licence

Text: **CC BY 4.0** (`LICENSE`). Code: **Apache-2.0** (`LICENSE-CODE`, `NOTICE`).
Canonical legal texts are linked, not retyped.

## Authorship

Volodymyr Sobol — author. AI models took part in the derivations, probes and texts;
they are named in `.zenodo.json` and, per artifact, in the git history
(`Co-Authored-By` trailers). Nothing is hidden and nothing contested is claimed.

## Citing

Archived on Zenodo. Cite the **concept DOI**, which always resolves to the latest
version — *(to be assigned on first release; this is a separate DOI series from
preprint-1)*. `citation.yaml` and the generated `CITATION.cff` carry the address
once minted. Both metadata files are generated from `citation.yaml` — **do not edit
them by hand**; edit the source and re-run the generator. The DOI is deliberately
absent from `.zenodo.json`: that field means "this record already carries an
external DOI", and putting our own there would silently break versioning on the
next release.
