import VGLean.A3Psi

set_option linter.style.header false
set_option linter.unusedSimpArgs false

/-!
# A3.5 (crown) — the concrete↔abstract `LieEquiv`  c(N)-core ≅ h₃ ⋊⁅ψ⁆ so(2,1)

The final A3 step: an explicit `LieEquiv` from the (3,2) rank-0 centralizer core (the A2 file `So32r0`,
`c(N) = sp(2,ℝ)⋉h₃`, dim 6) onto the abstract construct `H3 ⋊⁅ψ⁆ L21` built type-level in `A3Psi`.

`C6` is the abstract Lie algebra carrying the *exact* structure constants of `So32r0` (its bracket table
`brB_i_j`, machine-verified in A2 to be the brackets of the concrete so(3,2) matrices).  The alignment to
the construct's `H,E,F / X,Y,Z` basis is a clean index identification with **no scaling**:
`e₀↦inr F, e₁↦inr E, e₂↦inr H` (Levi = sl(2,ℝ), `B₂` is the Cartan) and `e₃↦inl X, e₄↦inl Y, e₅↦inl Z`
(module + centre).  `map_lie'` (bracket preservation both ways) is proven decidably (no native_decide).

Chain: concrete so(3,2) matrices —(A2, `So32r0.brB`: sc)→ `C6` —(this `LieEquiv`)→ `H₃ ⋊⁅ψ⁆ so(2,1)`.
This lifts the S946 isomorphism from a structure-constant match (A2) to a type-level `LieEquiv` (A3).
-/

open VGLean.A3 VGLean.A3.H3 VGLean.A3.L21 LieAlgebra

namespace VGLean.A3

/-- The abstract (3,2) rank-0 centralizer core, with `So32r0`'s exact structure constants. -/
def C6 := Fin 6 → ℚ

namespace C6

instance : AddCommGroup C6 := inferInstanceAs (AddCommGroup (Fin 6 → ℚ))
instance : Module ℚ C6 := inferInstanceAs (Module ℚ (Fin 6 → ℚ))

/-- Bracket from `So32r0.brB`: [B0,B1]=−B2, [B0,B2]=2B0, [B0,B3]=B4, [B1,B2]=−2B1, [B1,B4]=B3,
    [B2,B3]=B3, [B2,B4]=−B4, [B3,B4]=B5. -/
instance : Bracket C6 C6 :=
  ⟨fun u v => fun k =>
    if k = 0 then 2 * (u 0 * v 2 - u 2 * v 0)
    else if k = 1 then (-2) * (u 1 * v 2 - u 2 * v 1)
    else if k = 2 then -(u 0 * v 1 - u 1 * v 0)
    else if k = 3 then (u 1 * v 4 - u 4 * v 1) + (u 2 * v 3 - u 3 * v 2)
    else if k = 4 then (u 0 * v 3 - u 3 * v 0) - (u 2 * v 4 - u 4 * v 2)
    else (u 3 * v 4 - u 4 * v 3)⟩

@[simp] lemma bracket_apply (u v : C6) (k : Fin 6) :
    ⁅u, v⁆ k = (if k = 0 then 2 * (u 0 * v 2 - u 2 * v 0)
    else if k = 1 then (-2) * (u 1 * v 2 - u 2 * v 1)
    else if k = 2 then -(u 0 * v 1 - u 1 * v 0)
    else if k = 3 then (u 1 * v 4 - u 4 * v 1) + (u 2 * v 3 - u 3 * v 2)
    else if k = 4 then (u 0 * v 3 - u 3 * v 0) - (u 2 * v 4 - u 4 * v 2)
    else (u 3 * v 4 - u 4 * v 3)) := rfl
@[simp] lemma add_apply (u v : C6) (k : Fin 6) : (u + v) k = u k + v k := rfl
@[simp] lemma sub_apply (u v : C6) (k : Fin 6) : (u - v) k = u k - v k := rfl
@[simp] lemma neg_apply (u : C6) (k : Fin 6) : (-u) k = -(u k) := rfl
@[simp] lemma zero_apply (k : Fin 6) : (0 : C6) k = 0 := rfl
@[simp] lemma smul_apply (t : ℚ) (u : C6) (k : Fin 6) : (t • u) k = t * (u k) := rfl

macro "c6" : tactic => `(tactic| (funext k; fin_cases k <;> simp <;> ring))

instance : LieRing C6 where
  add_lie _ _ _ := by c6
  lie_add _ _ _ := by c6
  lie_self _ := by c6
  leibniz_lie _ _ _ := by c6

instance : LieAlgebra ℚ C6 where
  lie_smul _ _ _ := by c6

end C6

/-- Forward map `C6 → h₃ ⋊⁅ψ⁆ so(2,1)`: `e₀↦inr F, e₁↦inr E, e₂↦inr H, e₃↦inl X, e₄↦inl Y, e₅↦inl Z`.
    As a raw element: `u ↦ ⟨left=(u₃,u₄,u₅), right=(u₂,u₁,u₀)⟩`. -/
def toC (u : C6) : Construct :=
  ⟨fun i => if i = 0 then u 3 else if i = 1 then u 4 else u 5,
   fun i => if i = 0 then u 2 else if i = 1 then u 1 else u 0⟩

/-- Inverse map: `⟨k,l⟩ ↦ (l₂, l₁, l₀, k₀, k₁, k₂)`. -/
def ofC (x : Construct) : C6 :=
  fun i => if i = 0 then x.right 2 else if i = 1 then x.right 1 else if i = 2 then x.right 0
           else if i = 3 then x.left 0 else if i = 4 then x.left 1 else x.left 2

/-- The concrete↔abstract isomorphism `c(N)-core ≅ h₃ ⋊⁅ψ⁆ so(2,1)` as a `LieEquiv`. -/
def equiv : C6 ≃ₗ⁅ℚ⁆ Construct where
  toFun := toC
  invFun := ofC
  map_add' u v := by
    apply SemiDirectSum.ext <;> funext i <;> fin_cases i <;>
      simp [toC, SemiDirectSum.add_eq_mk]
  map_smul' t u := by
    apply SemiDirectSum.ext <;> funext i <;> fin_cases i <;>
      simp [toC, SemiDirectSum.smul_eq_mk, RingHom.id_apply]
  left_inv u := by funext i; fin_cases i <;> simp [ofC, toC]
  right_inv x := by
    apply SemiDirectSum.ext <;> funext i <;> fin_cases i <;> simp [ofC, toC]
  map_lie' {u v} := by
    apply SemiDirectSum.ext <;>
      (rw [SemiDirectSum.lie_eq_mk]; funext i; fin_cases i <;>
        simp [toC, psi, psiDer, psiLin, psiFun,
              H3.bracket_apply, L21.bracket_apply, C6.bracket_apply] <;> ring)

end VGLean.A3
