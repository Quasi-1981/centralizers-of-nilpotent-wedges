import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# A3 gap (1a) — the Heisenberg Lie algebra h₃ as an abstract `LieAlgebra ℚ`

mathlib (v4.32.0) has no named Heisenberg algebra (grep = 0), so A3 (the type-level
`SemiDirectSum` route) must define it by hand.  Here h₃ is the type synonym `Fin 3 → ℚ`
(coordinates x=·0, y=·1, z=·2 = centre) with the single non-trivial bracket
`⁅u,v⁆ = (u₀v₁ − u₁v₀)·e₂`.

Proven: the four `LieRing` axioms + the `LieAlgebra` scalar law (all decidable ℚ, no native_decide),
and the defining relations `⁅X,Y⁆ = Z`, `⁅X,Z⁆ = ⁅Y,Z⁆ = 0` (`z` central).  This is gap (1) of the
A3 plan (LEAN_ENDGAME_RECON §5): K = h₃ for the construct `h₃ ⋊⁅ψ⁆ so(2,1)`.
-/

namespace VGLean.A3

/-- The Heisenberg Lie algebra h₃ as a raw ℚ-vector space `Fin 3 → ℚ`. -/
def H3 := Fin 3 → ℚ

namespace H3

instance : AddCommGroup H3 := inferInstanceAs (AddCommGroup (Fin 3 → ℚ))
instance : Module ℚ H3 := inferInstanceAs (Module ℚ (Fin 3 → ℚ))

/-- Heisenberg bracket: only the centre (index 2) is fed, by the symplectic pairing of x,y. -/
instance : Bracket H3 H3 :=
  ⟨fun u v => fun i => if i = 2 then u 0 * v 1 - u 1 * v 0 else 0⟩

-- Pointwise `rfl` unfolders (the type synonym hides the Pi structure from `simp`).
@[simp] lemma bracket_apply (u v : H3) (i : Fin 3) :
    ⁅u, v⁆ i = if i = 2 then u 0 * v 1 - u 1 * v 0 else 0 := rfl
@[simp] lemma add_apply (u v : H3) (i : Fin 3) : (u + v) i = u i + v i := rfl
@[simp] lemma sub_apply (u v : H3) (i : Fin 3) : (u - v) i = u i - v i := rfl
@[simp] lemma neg_apply (u : H3) (i : Fin 3) : (-u) i = -(u i) := rfl
@[simp] lemma zero_apply (i : Fin 3) : (0 : H3) i = 0 := rfl
@[simp] lemma smul_apply (t : ℚ) (u : H3) (i : Fin 3) : (t • u) i = t * (u i) := rfl

/-- Entrywise decision tactic for abstract h₃. -/
macro "h3" : tactic => `(tactic| (funext i; fin_cases i <;> simp <;> ring))

instance : LieRing H3 where
  add_lie _ _ _ := by h3
  lie_add _ _ _ := by h3
  lie_self _ := by h3
  leibniz_lie _ _ _ := by h3

instance : LieAlgebra ℚ H3 where
  lie_smul _ _ _ := by h3

/-- Standard basis: `X = e₀`, `Y = e₁`, `Z = e₂` (the centre). -/
def X : H3 := fun i => if i = 0 then 1 else 0
def Y : H3 := fun i => if i = 1 then 1 else 0
def Z : H3 := fun i => if i = 2 then 1 else 0

/-- The single defining relation: `⁅X,Y⁆ = Z`. -/
theorem lie_X_Y : ⁅X, Y⁆ = Z := by
  funext i; fin_cases i <;> simp [X, Y, Z]

/-- `Z` central: `⁅X,Z⁆ = 0`. -/
theorem lie_X_Z : ⁅X, Z⁆ = 0 := by
  funext i; fin_cases i <;> simp [X, Z]

/-- `Z` central: `⁅Y,Z⁆ = 0`. -/
theorem lie_Y_Z : ⁅Y, Z⁆ = 0 := by
  funext i; fin_cases i <;> simp [Y, Z]

end H3
end VGLean.A3
