import VGLean.A3H3
import VGLean.A3So21

set_option linter.style.header false

/-!
# A3 gaps (2)+(3-construct) — the Levi action `ψ` and the semidirect construct `h₃ ⋊⁅ψ⁆ so(2,1)`

Gap (2): `ψ : so(2,1) →ₗ⁅ℚ⁆ LieDerivation ℚ h₃ h₃` — the sp(2,ℝ)-action of the Levi on the Heisenberg
algebra, built as a genuine Lie-algebra homomorphism into derivations (type-level, not matrices).
`ψ(l)` acts on the (x,y)-plane by the standard sl(2,ℝ)=sp(2,ℝ) representation and fixes the centre z;
the Leibniz rule and `map_lie'` (ψ⁅l,l'⁆ = ⁅ψl,ψl'⁆) are proven decidably (no native_decide).

Gap (3, construct half): the abstract construct `h₃ ⋊⁅ψ⁆ so(2,1)` via mathlib's native
`LieAlgebra.SemiDirectSum` (Leonid Ryvkin, v4.32.0) — a bona-fide `LieAlgebra ℚ` for free, with the
mixed bracket `⁅inr l, inl k⁆ = inl (ψ l k)` established.  This is the abstract target that the
concrete A2 centralizer `c(N)` (So32r0 = sp(2,ℝ)⋉h₃) maps onto (A3.5, the `LieEquiv`, is next).
-/

open VGLean.A3 VGLean.A3.H3 LieAlgebra

namespace VGLean.A3

/-- The sp(2,ℝ)-action of a Levi element `l` on h₃: acts on (x,y), fixes the centre z. -/
def psiFun (l : L21) (u : H3) : H3 := fun i =>
  if i = 0 then l 0 * u 0 + l 1 * u 1
  else if i = 1 then l 2 * u 0 - l 0 * u 1
  else 0

@[simp] lemma psiFun_apply (l : L21) (u : H3) (i : Fin 3) :
    psiFun l u i = (if i = 0 then l 0 * u 0 + l 1 * u 1
                    else if i = 1 then l 2 * u 0 - l 0 * u 1 else 0) := rfl

/-- `ψ(l)` as a linear map h₃ → h₃. -/
def psiLin (l : L21) : H3 →ₗ[ℚ] H3 where
  toFun := psiFun l
  map_add' u v := by funext i; fin_cases i <;> simp <;> ring
  map_smul' t u := by funext i; fin_cases i <;> simp <;> ring

@[simp] lemma psiLin_apply (l : L21) (u : H3) : psiLin l u = psiFun l u := rfl

/-- `ψ(l)` as a Lie derivation of h₃ (the sp action preserves the Heisenberg bracket). -/
def psiDer (l : L21) : LieDerivation ℚ H3 H3 where
  toLinearMap := psiLin l
  leibniz' a b := by funext i; fin_cases i <;> simp <;> ring

@[simp] lemma psiDer_apply (l : L21) (u : H3) : psiDer l u = psiFun l u := rfl

/-- The Levi action `ψ : so(2,1) → Der(h₃)` as a Lie-algebra homomorphism (gap 2). -/
def psi : L21 →ₗ⁅ℚ⁆ LieDerivation ℚ H3 H3 where
  toFun := psiDer
  map_add' l l' := by ext u; funext i; fin_cases i <;> simp <;> ring
  map_smul' t l := by ext u; funext i; fin_cases i <;> simp <;> ring
  map_lie' := by
    intro l l'
    ext u
    simp only [LieDerivation.commutator_apply, psiDer_apply]
    funext i; fin_cases i <;> simp [L21.bracket_apply, psiFun] <;> ring

@[simp] lemma psi_apply (l : L21) (u : H3) : psi l u = psiFun l u := rfl

/-- The abstract construct: `h₃ ⋊⁅ψ⁆ so(2,1)` (native `SemiDirectSum`, a `LieAlgebra ℚ` for free). -/
abbrev Construct := H3 ⋊⁅psi⁆ L21

-- The construct is a genuine Lie algebra (instances resolve).
example : LieAlgebra ℚ Construct := inferInstance

/-- Heisenberg sits inside as an ideal: `⁅inl k, inl k'⁆ = inl ⁅k,k'⁆`. -/
theorem lie_inl_inl (k k' : H3) :
    ⁅SemiDirectSum.inl psi k, SemiDirectSum.inl psi k'⁆ = SemiDirectSum.inl psi ⁅k, k'⁆ := by
  ext <;> simp [SemiDirectSum.lie_eq_mk]

/-- Levi sits inside as a subalgebra: `⁅inr l, inr l'⁆ = inr ⁅l,l'⁆`. -/
theorem lie_inr_inr (l l' : L21) :
    ⁅SemiDirectSum.inr psi l, SemiDirectSum.inr psi l'⁆ = SemiDirectSum.inr psi ⁅l, l'⁆ := by
  ext <;> simp [SemiDirectSum.lie_eq_mk]

/-- The semidirect twist: the Levi acts on the Heisenberg by `ψ` — `⁅inr l, inl k⁆ = inl (ψ l k)`. -/
theorem lie_inr_inl (l : L21) (k : H3) :
    ⁅SemiDirectSum.inr psi l, SemiDirectSum.inl psi k⁆ = SemiDirectSum.inl psi (psi l k) := by
  ext <;> simp [SemiDirectSum.lie_eq_mk]

end VGLean.A3
