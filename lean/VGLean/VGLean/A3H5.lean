import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# A3 gap (1a-h₅) — the Heisenberg Lie algebra h₅ as an abstract `LieAlgebra ℚ`

The 5-dimensional Heisenberg algebra for the deep n=6 rank-0 cores (So42r0/So33r0), whose full
centralizer is `(sp(2,ℝ) ⊕ so(η|G)) ⋉ h₅` (A2, dim 9).  Carrier `Fin 5 → ℚ`: coordinates 0..3 span the
4-dimensional symplectic module, coordinate 4 is the centre.  The symplectic pairing matches the concrete
So42r0/So33r0 module (`[m₀,m₂]=z`, `[m₁,m₃]=z`): `⁅u,v⁆ = ((u₀v₂−u₂v₀)+(u₁v₃−u₃v₁))·e₄`.

Same `rfl`-apply pattern as h₃ (A3H3).  Proven: the `LieRing`/`LieAlgebra` axioms + the defining bracket
relations (canonical pairs → centre, everything else central), all decidable ℚ (no native_decide).
Gap (1) of the A3 h₅ track: K = h₅ for the construct `h₅ ⋊⁅ψ⁆ (sp(2,ℝ)⊕so(η|G))`.
-/

namespace VGLean.A3

/-- The Heisenberg Lie algebra h₅ as a raw ℚ-vector space `Fin 5 → ℚ` (0..3 module, 4 = centre). -/
def H5 := Fin 5 → ℚ

namespace H5

instance : AddCommGroup H5 := inferInstanceAs (AddCommGroup (Fin 5 → ℚ))
instance : Module ℚ H5 := inferInstanceAs (Module ℚ (Fin 5 → ℚ))

/-- h₅ bracket: two symplectic pairs (0,2) and (1,3) feed the centre (index 4). -/
instance : Bracket H5 H5 :=
  ⟨fun u v => fun i =>
    if i = 4 then (u 0 * v 2 - u 2 * v 0) + (u 1 * v 3 - u 3 * v 1) else 0⟩

@[simp] lemma bracket_apply (u v : H5) (i : Fin 5) :
    ⁅u, v⁆ i = if i = 4 then (u 0 * v 2 - u 2 * v 0) + (u 1 * v 3 - u 3 * v 1) else 0 := rfl
@[simp] lemma add_apply (u v : H5) (i : Fin 5) : (u + v) i = u i + v i := rfl
@[simp] lemma sub_apply (u v : H5) (i : Fin 5) : (u - v) i = u i - v i := rfl
@[simp] lemma neg_apply (u : H5) (i : Fin 5) : (-u) i = -(u i) := rfl
@[simp] lemma zero_apply (i : Fin 5) : (0 : H5) i = 0 := rfl
@[simp] lemma smul_apply (t : ℚ) (u : H5) (i : Fin 5) : (t • u) i = t * (u i) := rfl

macro "h5" : tactic => `(tactic| (funext i; fin_cases i <;> simp <;> ring))

instance : LieRing H5 where
  add_lie _ _ _ := by h5
  lie_add _ _ _ := by h5
  lie_self _ := by h5
  leibniz_lie _ _ _ := by h5

instance : LieAlgebra ℚ H5 where
  lie_smul _ _ _ := by h5

/-- Module basis `P₀=e₀, P₁=e₁, Q₀=e₂, Q₁=e₃` and centre `Z=e₄`. -/
def P0 : H5 := fun i => if i = 0 then 1 else 0
def P1 : H5 := fun i => if i = 1 then 1 else 0
def Q0 : H5 := fun i => if i = 2 then 1 else 0
def Q1 : H5 := fun i => if i = 3 then 1 else 0
def Z  : H5 := fun i => if i = 4 then 1 else 0

theorem lie_P0_Q0 : ⁅P0, Q0⁆ = Z := by funext i; fin_cases i <;> simp [P0, Q0, Z]
theorem lie_P1_Q1 : ⁅P1, Q1⁆ = Z := by funext i; fin_cases i <;> simp [P1, Q1, Z]
theorem lie_P0_P1 : ⁅P0, P1⁆ = 0 := by funext i; fin_cases i <;> simp [P0, P1]
theorem lie_P0_Q1 : ⁅P0, Q1⁆ = 0 := by funext i; fin_cases i <;> simp [P0, Q1]
theorem lie_Q0_Q1 : ⁅Q0, Q1⁆ = 0 := by funext i; fin_cases i <;> simp [Q0, Q1]
theorem lie_P0_Z : ⁅P0, Z⁆ = 0 := by funext i; fin_cases i <;> simp [P0, Z]

end H5
end VGLean.A3
