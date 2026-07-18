import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# A1 — first instance: the `(2,2)` rank-0 wedge centralizer, machine-checked

The smallest non-abelian wedge centralizer of the W33 ladder (Т17/Т18 §12).
Ambient `so(η)`, `η = diag(1,1,-1,-1)` (= `indefiniteDiagonal (2,2)`, the metric
of mathlib's `so'(2,2)`).  `N` is the rank-2 isotropic wedge; `g0..g3` span the
4-dimensional centralizer `c(N)` (probe S933: `dimc=4, dim[c,c]=3, dimZ=1`, i.e.
`so(2,1) ⊕ ℝ`).  Data frozen by `lean/artifacts/gen_A1_so21.py` (exact rational
identities), which cross-checks the probe's flag-metric table up to basis sign.

What is proved here (fourth verification layer, all by decidable ℚ arithmetic):
* `N` is nilpotent (`N*N = 0`) and skew-adjoint for `η` (`N ∈ so(η)`);
* each `gᵢ ∈ so(η)` and commutes with `N` (`⁅gᵢ,N⁆ = 0`, the centralizer law);
* the full bracket table of `g0..g3` closes with the measured structure constants.

This is *verification of a proven result*, not a new verdict.  A red check would
be a finding, reported loudly — the build being green is the point.
-/

namespace VGLean.So21

open Matrix

abbrev M4 := Matrix (Fin 4) (Fin 4) ℚ

/-- Indefinite metric `diag(1,1,-1,-1)` — the `(2,2)` signature. -/
def η : M4 := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]

/-- Rank-2 isotropic nilpotent wedge `N = x∧y`, `x=e₀+e₂`, `y=e₁+e₃`. -/
def N : M4 := !![0,-1,0,1; 1,0,-1,0; 0,-1,0,1; 1,0,-1,0]

/-- Centralizer generators (a basis of `c(N)`, frozen artifact). -/
def g0 : M4 := !![0,-1,0,1; 1,0,0,0; 0,0,0,0; 1,0,0,0]
def g1 : M4 := !![0,1,0,0; -1,0,1,0; 0,1,0,0; 0,0,0,0]
def g2 : M4 := !![0,0,-1,0; 0,0,0,1; -1,0,0,0; 0,1,0,0]
def g3 : M4 := !![0,-1,0,0; 1,0,0,0; 0,0,0,-1; 0,0,1,0]

/-- Membership in `so(η)`: skew-adjointness `Mᵀ η + η M = 0`. -/
def inSO (A : M4) : Prop := Aᵀ * η + η * A = 0

/-- Matrix commutator (the Lie bracket on `Matrix`). -/
def commutator (A B : M4) : M4 := A * B - B * A

/-- Entrywise decision procedure for concrete `!!` matrices over `ℚ`. -/
macro "mat" : tactic =>
  `(tactic| (apply Matrix.ext; intro i j;
             fin_cases i <;> fin_cases j <;>
             simp [η, N, g0, g1, g2, g3, inSO, commutator, Matrix.mul_apply,
                   Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply,
                   Matrix.smul_apply, Matrix.zero_apply, Fin.sum_univ_four] <;>
             norm_num))

-- N is a rank-2 nilpotent.
theorem N_nilpotent : N * N = 0 := by mat

-- N and every generator lie in so(η).
theorem N_inSO : inSO N := by mat
theorem g0_inSO : inSO g0 := by mat
theorem g1_inSO : inSO g1 := by mat
theorem g2_inSO : inSO g2 := by mat
theorem g3_inSO : inSO g3 := by mat

-- Centralizer law: each generator commutes with N.
theorem g0_comm : commutator g0 N = 0 := by mat
theorem g1_comm : commutator g1 N = 0 := by mat
theorem g2_comm : commutator g2 N = 0 := by mat
theorem g3_comm : commutator g3 N = 0 := by mat

-- Bracket table (structure constants of c(N) in the basis g0..g3).
theorem br_01 : commutator g0 g1 = g2 := by mat
theorem br_02 : commutator g0 g2 = -g0 - g1 - g3 := by mat
theorem br_03 : commutator g0 g3 = -g2 := by mat
theorem br_12 : commutator g1 g2 = g0 + g1 - g3 := by mat
theorem br_13 : commutator g1 g3 = -g2 := by mat
theorem br_23 : commutator g2 g3 = (2:ℚ) • g0 + (2:ℚ) • g1 := by mat

end VGLean.So21
