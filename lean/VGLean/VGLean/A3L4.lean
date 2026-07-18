import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# A3 gap (1b-h₅) — the reductive Levi `L4 = sp(2,ℝ) ⊕ so(η|G)` as an abstract `LieAlgebra ℚ`

The 4-dimensional reductive Levi of the deep n=6 rank-0 centralizers (So42r0/So33r0): the simple
`sp(2,ℝ) ≅ sl(2,ℝ)` (basis `H=e₀, E=e₁, F=e₂`) in direct sum with the 1-dimensional reductive centre
`so(η|G) = ℝ·W` (`W=e₃`, central).  `W` is central in `L4` for **both** signature cases — the
compact-so(2)/boost-so(1,1) difference lives entirely in the *action* `ψ` (A3Psi-h₅), not in `L4` itself.

Proven: the `LieRing`/`LieAlgebra` axioms + defining relations (`⁅H,E⁆=2E, ⁅H,F⁆=−2F, ⁅E,F⁆=H`, `W`
central), all decidable ℚ (no native_decide).  Gap (1b) of the A3 h₅ track.
-/

namespace VGLean.A3

/-- The reductive Levi `sp(2,ℝ) ⊕ ℝ·W` as `Fin 4 → ℚ` (0,1,2 = sl(2,ℝ); 3 = central W). -/
def L4 := Fin 4 → ℚ

namespace L4

instance : AddCommGroup L4 := inferInstanceAs (AddCommGroup (Fin 4 → ℚ))
instance : Module ℚ L4 := inferInstanceAs (Module ℚ (Fin 4 → ℚ))

/-- sl(2,ℝ) on 0,1,2 (`H,E,F`); `W` (index 3) central. -/
instance : Bracket L4 L4 :=
  ⟨fun u v => fun i =>
    if i = 0 then u 1 * v 2 - u 2 * v 1
    else if i = 1 then 2 * (u 0 * v 1 - u 1 * v 0)
    else if i = 2 then (-2) * (u 0 * v 2 - u 2 * v 0)
    else 0⟩

@[simp] lemma bracket_apply (u v : L4) (i : Fin 4) :
    ⁅u, v⁆ i = (if i = 0 then u 1 * v 2 - u 2 * v 1
                else if i = 1 then 2 * (u 0 * v 1 - u 1 * v 0)
                else if i = 2 then (-2) * (u 0 * v 2 - u 2 * v 0)
                else 0) := rfl
@[simp] lemma add_apply (u v : L4) (i : Fin 4) : (u + v) i = u i + v i := rfl
@[simp] lemma sub_apply (u v : L4) (i : Fin 4) : (u - v) i = u i - v i := rfl
@[simp] lemma neg_apply (u : L4) (i : Fin 4) : (-u) i = -(u i) := rfl
@[simp] lemma zero_apply (i : Fin 4) : (0 : L4) i = 0 := rfl
@[simp] lemma smul_apply (t : ℚ) (u : L4) (i : Fin 4) : (t • u) i = t * (u i) := rfl

macro "l4" : tactic => `(tactic| (funext i; fin_cases i <;> simp <;> ring))

instance : LieRing L4 where
  add_lie _ _ _ := by l4
  lie_add _ _ _ := by l4
  lie_self _ := by l4
  leibniz_lie _ _ _ := by l4

instance : LieAlgebra ℚ L4 where
  lie_smul _ _ _ := by l4

/-- Basis: `H=e₀, E=e₁, F=e₂, W=e₃` (`W` the reductive centre). -/
def H : L4 := fun i => if i = 0 then 1 else 0
def E : L4 := fun i => if i = 1 then 1 else 0
def F : L4 := fun i => if i = 2 then 1 else 0
def W : L4 := fun i => if i = 3 then 1 else 0

theorem lie_H_E : ⁅H, E⁆ = (2 : ℚ) • E := by funext i; fin_cases i <;> simp [H, E]
theorem lie_H_F : ⁅H, F⁆ = (-2 : ℚ) • F := by funext i; fin_cases i <;> simp [H, F]
theorem lie_E_F : ⁅E, F⁆ = H := by funext i; fin_cases i <;> simp [E, F, H]
theorem lie_H_W : ⁅H, W⁆ = 0 := by funext i; fin_cases i <;> simp [H, W]
theorem lie_E_W : ⁅E, W⁆ = 0 := by funext i; fin_cases i <;> simp [E, W]
theorem lie_F_W : ⁅F, W⁆ = 0 := by funext i; fin_cases i <;> simp [F, W]

end L4
end VGLean.A3
