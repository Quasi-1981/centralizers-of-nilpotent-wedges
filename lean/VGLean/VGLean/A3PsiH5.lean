import VGLean.A3H5
import VGLean.A3L4

set_option linter.style.header false

/-!
# A3 gaps (2)+(construct)-h₅ — the two Levi actions `ψ` and the constructs `h₅ ⋊⁅ψ⁆ L4`

Gap (2) for the deep n=6 rank-0 cores: `ψ : L4 →ₗ⁅ℚ⁆ LieDerivation ℚ h₅ h₅`, the action of the reductive
Levi `L4 = sp(2,ℝ) ⊕ ℝ·W` on the Heisenberg algebra h₅.  The `sp(2,ℝ)` part acts by the standard symplectic
representation on the two canonical pairs `(P₀,Q₀), (P₁,Q₁)`; the reductive centre `W` acts by the
signature-selected generator — **two cases**:

* `psi5C` — the **compact** case (So42r0, signature (4,2)): `W` is the rotation `so(2)`
  (`P₀↦−P₁, P₁↦P₀, Q₀↦−Q₁, Q₁↦Q₀`);
* `psi5B` — the **boost** case (So33r0, signature (3,3)): `W` is the split `so(1,1)` boost
  (`P₀↦P₁, P₁↦P₀, Q₀↦−Q₁, Q₁↦−Q₀`).

Both are genuine derivation homomorphisms (Leibniz + `map_lie'`), proven decidably (no native_decide).
The two constructs `h₅ ⋊⁅ψ⁆ L4` are the abstract targets for the A2 cores So42r0/So33r0 (dim 9); the
compact/boost split is exactly the `B8_cube` eigenvalue-type invariant, lifted to the action.
-/

open VGLean.A3 VGLean.A3.H5 LieAlgebra

namespace VGLean.A3

/-! ### Compact case (So42r0, (4,2)) — W acts as so(2) rotation -/

def psiFun5C (l : L4) (u : H5) : H5 := fun i =>
  if i = 0 then l 0 * u 0 + l 1 * u 2 + l 3 * u 1
  else if i = 1 then l 0 * u 1 + l 1 * u 3 - l 3 * u 0
  else if i = 2 then -(l 0) * u 2 + l 2 * u 0 + l 3 * u 3
  else if i = 3 then -(l 0) * u 3 + l 2 * u 1 - l 3 * u 2
  else 0

@[simp] lemma psiFun5C_apply (l : L4) (u : H5) (i : Fin 5) :
    psiFun5C l u i = (if i = 0 then l 0 * u 0 + l 1 * u 2 + l 3 * u 1
      else if i = 1 then l 0 * u 1 + l 1 * u 3 - l 3 * u 0
      else if i = 2 then -(l 0) * u 2 + l 2 * u 0 + l 3 * u 3
      else if i = 3 then -(l 0) * u 3 + l 2 * u 1 - l 3 * u 2 else 0) := rfl

def psiLin5C (l : L4) : H5 →ₗ[ℚ] H5 where
  toFun := psiFun5C l
  map_add' u v := by funext i; fin_cases i <;> simp <;> ring
  map_smul' t u := by funext i; fin_cases i <;> simp <;> ring

@[simp] lemma psiLin5C_apply (l : L4) (u : H5) : psiLin5C l u = psiFun5C l u := rfl

def psiDer5C (l : L4) : LieDerivation ℚ H5 H5 where
  toLinearMap := psiLin5C l
  leibniz' a b := by funext i; fin_cases i <;> simp <;> ring

@[simp] lemma psiDer5C_apply (l : L4) (u : H5) : psiDer5C l u = psiFun5C l u := rfl

/-- Compact Levi action `ψ : L4 → Der(h₅)` (W = so(2) rotation). -/
def psi5C : L4 →ₗ⁅ℚ⁆ LieDerivation ℚ H5 H5 where
  toFun := psiDer5C
  map_add' l l' := by ext u; funext i; fin_cases i <;> simp <;> ring
  map_smul' t l := by ext u; funext i; fin_cases i <;> simp <;> ring
  map_lie' := by
    intro l l'; ext u
    simp only [LieDerivation.commutator_apply, psiDer5C_apply]
    funext i; fin_cases i <;> simp [L4.bracket_apply, psiFun5C] <;> ring

/-- The compact construct `h₅ ⋊⁅ψ5C⁆ (sp(2,ℝ)⊕so(2))` — target for So42r0. -/
abbrev ConstructC := H5 ⋊⁅psi5C⁆ L4
example : LieAlgebra ℚ ConstructC := inferInstance

/-! ### Boost case (So33r0, (3,3)) — W acts as so(1,1) split boost -/

-- Signature effect: in (3,3) the SECOND symplectic pair (P₁,Q₁) carries the opposite sl(2,ℝ)
-- orientation (`E: Q₁↦−P₁`, `F: P₁↦−Q₁`), and W is the split so(1,1) boost.
def psiFun5B (l : L4) (u : H5) : H5 := fun i =>
  if i = 0 then l 0 * u 0 + l 1 * u 2 + l 3 * u 1
  else if i = 1 then l 0 * u 1 - l 1 * u 3 + l 3 * u 0
  else if i = 2 then -(l 0) * u 2 + l 2 * u 0 - l 3 * u 3
  else if i = 3 then -(l 0) * u 3 - l 2 * u 1 - l 3 * u 2
  else 0

@[simp] lemma psiFun5B_apply (l : L4) (u : H5) (i : Fin 5) :
    psiFun5B l u i = (if i = 0 then l 0 * u 0 + l 1 * u 2 + l 3 * u 1
      else if i = 1 then l 0 * u 1 - l 1 * u 3 + l 3 * u 0
      else if i = 2 then -(l 0) * u 2 + l 2 * u 0 - l 3 * u 3
      else if i = 3 then -(l 0) * u 3 - l 2 * u 1 - l 3 * u 2 else 0) := rfl

def psiLin5B (l : L4) : H5 →ₗ[ℚ] H5 where
  toFun := psiFun5B l
  map_add' u v := by funext i; fin_cases i <;> simp <;> ring
  map_smul' t u := by funext i; fin_cases i <;> simp <;> ring

@[simp] lemma psiLin5B_apply (l : L4) (u : H5) : psiLin5B l u = psiFun5B l u := rfl

def psiDer5B (l : L4) : LieDerivation ℚ H5 H5 where
  toLinearMap := psiLin5B l
  leibniz' a b := by funext i; fin_cases i <;> simp <;> ring

@[simp] lemma psiDer5B_apply (l : L4) (u : H5) : psiDer5B l u = psiFun5B l u := rfl

/-- Boost Levi action `ψ : L4 → Der(h₅)` (W = so(1,1) boost). -/
def psi5B : L4 →ₗ⁅ℚ⁆ LieDerivation ℚ H5 H5 where
  toFun := psiDer5B
  map_add' l l' := by ext u; funext i; fin_cases i <;> simp <;> ring
  map_smul' t l := by ext u; funext i; fin_cases i <;> simp <;> ring
  map_lie' := by
    intro l l'; ext u
    simp only [LieDerivation.commutator_apply, psiDer5B_apply]
    funext i; fin_cases i <;> simp [L4.bracket_apply, psiFun5B] <;> ring

/-- The boost construct `h₅ ⋊⁅ψ5B⁆ (sp(2,ℝ)⊕so(1,1))` — target for So33r0. -/
abbrev ConstructB := H5 ⋊⁅psi5B⁆ L4
example : LieAlgebra ℚ ConstructB := inferInstance

end VGLean.A3
