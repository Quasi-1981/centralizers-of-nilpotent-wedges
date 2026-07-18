import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# A3 gap (1b) — the Levi `so(2,1) ≅ sl(2,ℝ) ≅ sp(2,ℝ)` as an abstract `LieAlgebra ℚ`

The 3-dimensional simple Levi of the A2 rank-0 wedge centralizers, defined type-level (not as a matrix
subalgebra) so it can serve as `L` in the construct `h₃ ⋊⁅ψ⁆ so(2,1)` (A3 plan, LEAN_ENDGAME_RECON §5).

Carrier: `Fin 3 → ℚ` with the sl(2,ℝ) basis `H=e₀, E=e₁, F=e₂` and brackets
`⁅H,E⁆=2E, ⁅H,F⁆=−2F, ⁅E,F⁆=H`.  Proven: the `LieRing`/`LieAlgebra` axioms (incl. Jacobi) + the three
defining relations, all decidable ℚ (no native_decide).
-/

namespace VGLean.A3

/-- The Levi `so(2,1) ≅ sl(2,ℝ) ≅ sp(2,ℝ)` as a raw ℚ-vector space `Fin 3 → ℚ`. -/
def L21 := Fin 3 → ℚ

namespace L21

instance : AddCommGroup L21 := inferInstanceAs (AddCommGroup (Fin 3 → ℚ))
instance : Module ℚ L21 := inferInstanceAs (Module ℚ (Fin 3 → ℚ))

/-- sl(2,ℝ) bracket in the `H=e₀, E=e₁, F=e₂` basis (structure constants of ⁅H,E⁆=2E etc.). -/
instance : Bracket L21 L21 :=
  ⟨fun u v => fun i =>
    if i = 0 then u 1 * v 2 - u 2 * v 1
    else if i = 1 then 2 * (u 0 * v 1 - u 1 * v 0)
    else (-2) * (u 0 * v 2 - u 2 * v 0)⟩

@[simp] lemma bracket_apply (u v : L21) (i : Fin 3) :
    ⁅u, v⁆ i = (if i = 0 then u 1 * v 2 - u 2 * v 1
                else if i = 1 then 2 * (u 0 * v 1 - u 1 * v 0)
                else (-2) * (u 0 * v 2 - u 2 * v 0)) := rfl
@[simp] lemma add_apply (u v : L21) (i : Fin 3) : (u + v) i = u i + v i := rfl
@[simp] lemma sub_apply (u v : L21) (i : Fin 3) : (u - v) i = u i - v i := rfl
@[simp] lemma neg_apply (u : L21) (i : Fin 3) : (-u) i = -(u i) := rfl
@[simp] lemma zero_apply (i : Fin 3) : (0 : L21) i = 0 := rfl
@[simp] lemma smul_apply (t : ℚ) (u : L21) (i : Fin 3) : (t • u) i = t * (u i) := rfl

/-- Entrywise decision tactic for abstract sl(2,ℝ). -/
macro "l21" : tactic => `(tactic| (funext i; fin_cases i <;> simp <;> ring))

instance : LieRing L21 where
  add_lie _ _ _ := by l21
  lie_add _ _ _ := by l21
  lie_self _ := by l21
  leibniz_lie _ _ _ := by l21

instance : LieAlgebra ℚ L21 where
  lie_smul _ _ _ := by l21

/-- Basis: `H = e₀`, `E = e₁`, `F = e₂`. -/
def H : L21 := fun i => if i = 0 then 1 else 0
def E : L21 := fun i => if i = 1 then 1 else 0
def F : L21 := fun i => if i = 2 then 1 else 0

theorem lie_H_E : ⁅H, E⁆ = (2 : ℚ) • E := by funext i; fin_cases i <;> simp [H, E]
theorem lie_H_F : ⁅H, F⁆ = (-2 : ℚ) • F := by funext i; fin_cases i <;> simp [H, F]
theorem lie_E_F : ⁅E, F⁆ = H := by funext i; fin_cases i <;> simp [E, F, H]

end L21
end VGLean.A3
