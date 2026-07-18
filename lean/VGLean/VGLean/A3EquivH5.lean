import VGLean.A3PsiH5

set_option linter.style.header false
set_option linter.unusedSimpArgs false

/-!
# A3.5-h₅ (crown) — concrete↔abstract `LieEquiv` for the deep n=6 rank-0 centralizers

The h₅ crowns: explicit `LieEquiv` from the (4,2)/(3,3) rank-0 centralizer cores (A2 files So42r0/So33r0,
`c(N) = (sp(2,ℝ)⊕so(η|G))⋉h₅`, dim 9) onto the abstract constructs `h₅ ⋊⁅ψ⁆ L4` (A3PsiH5, compact ψ5C /
boost ψ5B).  `C9C`/`C9B` carry the exact So42r0/So33r0 structure constants (A2 `brB`, machine-verified to
be the brackets of the concrete so(p,q) matrices).  The alignment is the monomial map (scales solved and
sc-verified in `gen_A3_equiv_h5.py`, FULL match both cases):

  B0↦H, B1↦−4E, B2↦F, B3↦P0, B4↦−P1, B5↦−½Q0, B6↦½Q1, B7↦−½Z, B8↦−W.

`map_lie'` (bracket preservation both ways) is proven decidably (no native_decide).  This closes A3 for the
deep n=6 rank-0 family, lifting the S946 isomorphism to a type-level `LieEquiv` for both signature cases
(the compact/boost split of the reductive centre lives in ψ5C vs ψ5B — the `B8_cube` invariant).
-/

open VGLean.A3 VGLean.A3.H5 VGLean.A3.L4 LieAlgebra

namespace VGLean.A3

/-- Abstract `C9C` = the rank-0 core with the exact C9C structure constants. -/
def C9C := Fin 9 → ℚ
namespace C9C
instance : AddCommGroup C9C := inferInstanceAs (AddCommGroup (Fin 9 → ℚ))
instance : Module ℚ C9C := inferInstanceAs (Module ℚ (Fin 9 → ℚ))
instance : Bracket C9C C9C :=
  ⟨fun u v => fun i =>
    if i = 0 then (-4) * (u 1 * v 2 - u 2 * v 1)
    else if i = 1 then (2) * (u 0 * v 1 - u 1 * v 0)
    else if i = 2 then (-2) * (u 0 * v 2 - u 2 * v 0)
    else if i = 3 then (u 0 * v 3 - u 3 * v 0) + (2) * (u 1 * v 5 - u 5 * v 1) - (u 4 * v 8 - u 8 * v 4)
    else if i = 4 then (u 0 * v 4 - u 4 * v 0) + (2) * (u 1 * v 6 - u 6 * v 1) + (u 3 * v 8 - u 8 * v 3)
    else if i = 5 then -(u 0 * v 5 - u 5 * v 0) + (-2) * (u 2 * v 3 - u 3 * v 2) - (u 6 * v 8 - u 8 * v 6)
    else if i = 6 then -(u 0 * v 6 - u 6 * v 0) + (-2) * (u 2 * v 4 - u 4 * v 2) + (u 5 * v 8 - u 8 * v 5)
    else if i = 7 then (u 3 * v 5 - u 5 * v 3) + (u 4 * v 6 - u 6 * v 4)
    else 0⟩
@[simp] lemma bracket_apply (u v : C9C) (i : Fin 9) :
    ⁅u, v⁆ i = (
      if i = 0 then (-4) * (u 1 * v 2 - u 2 * v 1)
      else if i = 1 then (2) * (u 0 * v 1 - u 1 * v 0)
      else if i = 2 then (-2) * (u 0 * v 2 - u 2 * v 0)
      else if i = 3 then (u 0 * v 3 - u 3 * v 0) + (2) * (u 1 * v 5 - u 5 * v 1) - (u 4 * v 8 - u 8 * v 4)
      else if i = 4 then (u 0 * v 4 - u 4 * v 0) + (2) * (u 1 * v 6 - u 6 * v 1) + (u 3 * v 8 - u 8 * v 3)
      else if i = 5 then -(u 0 * v 5 - u 5 * v 0) + (-2) * (u 2 * v 3 - u 3 * v 2) - (u 6 * v 8 - u 8 * v 6)
      else if i = 6 then -(u 0 * v 6 - u 6 * v 0) + (-2) * (u 2 * v 4 - u 4 * v 2) + (u 5 * v 8 - u 8 * v 5)
      else if i = 7 then (u 3 * v 5 - u 5 * v 3) + (u 4 * v 6 - u 6 * v 4)
      else 0) := rfl
@[simp] lemma add_apply (u v : C9C) (i : Fin 9) : (u + v) i = u i + v i := rfl
@[simp] lemma sub_apply (u v : C9C) (i : Fin 9) : (u - v) i = u i - v i := rfl
@[simp] lemma neg_apply (u : C9C) (i : Fin 9) : (-u) i = -(u i) := rfl
@[simp] lemma zero_apply (i : Fin 9) : (0 : C9C) i = 0 := rfl
@[simp] lemma smul_apply (t : ℚ) (u : C9C) (i : Fin 9) : (t • u) i = t * (u i) := rfl
macro "c9" : tactic => `(tactic| (funext i; fin_cases i <;> simp <;> ring))
instance : LieRing C9C where
  add_lie _ _ _ := by c9
  lie_add _ _ _ := by c9
  lie_self _ := by c9
  leibniz_lie _ _ _ := by c9
instance : LieAlgebra ℚ C9C where
  lie_smul _ _ _ := by c9
end C9C

/-- Forward map `C9C → ConstructC` (monomial alignment, scales solved + sc-verified). -/
def toC_C (u : C9C) : ConstructC :=
  ⟨fun i => if i = 0 then u 3 else if i = 1 then -u 4 else if i = 2 then (-1/2) * u 5 else if i = 3 then (1/2) * u 6 else (-1/2) * u 7,
   fun i => if i = 0 then u 0 else if i = 1 then (-4) * u 1 else if i = 2 then u 2 else -u 8⟩
def ofC_C (x : ConstructC) : C9C :=
  fun i => if i = 0 then x.right 0 else if i = 1 then (-1/4) * x.right 1 else if i = 2 then x.right 2 else if i = 3 then x.left 0 else if i = 4 then -x.left 1 else if i = 5 then (-2) * x.left 2 else if i = 6 then (2) * x.left 3 else if i = 7 then (-2) * x.left 4 else -x.right 3
/-- The concrete↔abstract `LieEquiv` for the C core. -/
def equiv_C : C9C ≃ₗ⁅ℚ⁆ ConstructC where
  toFun := toC_C
  invFun := ofC_C
  map_add' u v := by
    apply SemiDirectSum.ext <;> funext i <;> fin_cases i <;>
      simp [toC_C, SemiDirectSum.add_eq_mk] <;> ring
  map_smul' t u := by
    apply SemiDirectSum.ext <;> funext i <;> fin_cases i <;>
      simp [toC_C, SemiDirectSum.smul_eq_mk, RingHom.id_apply] <;> ring
  left_inv u := by funext i; fin_cases i <;> simp [ofC_C, toC_C] <;> ring
  right_inv x := by
    apply SemiDirectSum.ext <;> funext i <;> fin_cases i <;>
      simp [ofC_C, toC_C] <;> ring
  map_lie' {u v} := by
    apply SemiDirectSum.ext <;>
      (rw [SemiDirectSum.lie_eq_mk]; funext i; fin_cases i <;>
        simp [toC_C, psiDer5C, psiLin5C, psi5C,
              H5.bracket_apply, L4.bracket_apply, C9C.bracket_apply] <;> ring)

/-- Abstract `C9B` = the rank-0 core with the exact C9B structure constants. -/
def C9B := Fin 9 → ℚ
namespace C9B
instance : AddCommGroup C9B := inferInstanceAs (AddCommGroup (Fin 9 → ℚ))
instance : Module ℚ C9B := inferInstanceAs (Module ℚ (Fin 9 → ℚ))
instance : Bracket C9B C9B :=
  ⟨fun u v => fun i =>
    if i = 0 then (-4) * (u 1 * v 2 - u 2 * v 1)
    else if i = 1 then (2) * (u 0 * v 1 - u 1 * v 0)
    else if i = 2 then (-2) * (u 0 * v 2 - u 2 * v 0)
    else if i = 3 then (u 0 * v 3 - u 3 * v 0) + (2) * (u 1 * v 5 - u 5 * v 1) - (u 4 * v 8 - u 8 * v 4)
    else if i = 4 then (u 0 * v 4 - u 4 * v 0) + (-2) * (u 1 * v 6 - u 6 * v 1) - (u 3 * v 8 - u 8 * v 3)
    else if i = 5 then -(u 0 * v 5 - u 5 * v 0) + (-2) * (u 2 * v 3 - u 3 * v 2) + (u 6 * v 8 - u 8 * v 6)
    else if i = 6 then -(u 0 * v 6 - u 6 * v 0) + (2) * (u 2 * v 4 - u 4 * v 2) + (u 5 * v 8 - u 8 * v 5)
    else if i = 7 then (u 3 * v 5 - u 5 * v 3) + (u 4 * v 6 - u 6 * v 4)
    else 0⟩
@[simp] lemma bracket_apply (u v : C9B) (i : Fin 9) :
    ⁅u, v⁆ i = (
      if i = 0 then (-4) * (u 1 * v 2 - u 2 * v 1)
      else if i = 1 then (2) * (u 0 * v 1 - u 1 * v 0)
      else if i = 2 then (-2) * (u 0 * v 2 - u 2 * v 0)
      else if i = 3 then (u 0 * v 3 - u 3 * v 0) + (2) * (u 1 * v 5 - u 5 * v 1) - (u 4 * v 8 - u 8 * v 4)
      else if i = 4 then (u 0 * v 4 - u 4 * v 0) + (-2) * (u 1 * v 6 - u 6 * v 1) - (u 3 * v 8 - u 8 * v 3)
      else if i = 5 then -(u 0 * v 5 - u 5 * v 0) + (-2) * (u 2 * v 3 - u 3 * v 2) + (u 6 * v 8 - u 8 * v 6)
      else if i = 6 then -(u 0 * v 6 - u 6 * v 0) + (2) * (u 2 * v 4 - u 4 * v 2) + (u 5 * v 8 - u 8 * v 5)
      else if i = 7 then (u 3 * v 5 - u 5 * v 3) + (u 4 * v 6 - u 6 * v 4)
      else 0) := rfl
@[simp] lemma add_apply (u v : C9B) (i : Fin 9) : (u + v) i = u i + v i := rfl
@[simp] lemma sub_apply (u v : C9B) (i : Fin 9) : (u - v) i = u i - v i := rfl
@[simp] lemma neg_apply (u : C9B) (i : Fin 9) : (-u) i = -(u i) := rfl
@[simp] lemma zero_apply (i : Fin 9) : (0 : C9B) i = 0 := rfl
@[simp] lemma smul_apply (t : ℚ) (u : C9B) (i : Fin 9) : (t • u) i = t * (u i) := rfl
macro "c9" : tactic => `(tactic| (funext i; fin_cases i <;> simp <;> ring))
instance : LieRing C9B where
  add_lie _ _ _ := by c9
  lie_add _ _ _ := by c9
  lie_self _ := by c9
  leibniz_lie _ _ _ := by c9
instance : LieAlgebra ℚ C9B where
  lie_smul _ _ _ := by c9
end C9B

/-- Forward map `C9B → ConstructB` (monomial alignment, scales solved + sc-verified). -/
def toC_B (u : C9B) : ConstructB :=
  ⟨fun i => if i = 0 then u 3 else if i = 1 then -u 4 else if i = 2 then (-1/2) * u 5 else if i = 3 then (1/2) * u 6 else (-1/2) * u 7,
   fun i => if i = 0 then u 0 else if i = 1 then (-4) * u 1 else if i = 2 then u 2 else -u 8⟩
def ofC_B (x : ConstructB) : C9B :=
  fun i => if i = 0 then x.right 0 else if i = 1 then (-1/4) * x.right 1 else if i = 2 then x.right 2 else if i = 3 then x.left 0 else if i = 4 then -x.left 1 else if i = 5 then (-2) * x.left 2 else if i = 6 then (2) * x.left 3 else if i = 7 then (-2) * x.left 4 else -x.right 3
/-- The concrete↔abstract `LieEquiv` for the B core. -/
def equiv_B : C9B ≃ₗ⁅ℚ⁆ ConstructB where
  toFun := toC_B
  invFun := ofC_B
  map_add' u v := by
    apply SemiDirectSum.ext <;> funext i <;> fin_cases i <;>
      simp [toC_B, SemiDirectSum.add_eq_mk] <;> ring
  map_smul' t u := by
    apply SemiDirectSum.ext <;> funext i <;> fin_cases i <;>
      simp [toC_B, SemiDirectSum.smul_eq_mk, RingHom.id_apply] <;> ring
  left_inv u := by funext i; fin_cases i <;> simp [ofC_B, toC_B] <;> ring
  right_inv x := by
    apply SemiDirectSum.ext <;> funext i <;> fin_cases i <;>
      simp [ofC_B, toC_B] <;> ring
  map_lie' {u v} := by
    apply SemiDirectSum.ext <;>
      (rw [SemiDirectSum.lie_eq_mk]; funext i; fin_cases i <;>
        simp [toC_B, psiDer5B, psiLin5B, psi5B,
              H5.bracket_apply, L4.bracket_apply, C9B.bracket_apply] <;> ring)

end VGLean.A3
