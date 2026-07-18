import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000   -- dense 8×8 so(4,4) entrywise checks

/-!
# S988 kernel-check — so(4,4) two-wedge rank-4 (saturating, n=8): centralizer c(N) in so(4,4)
Alpha's export S988 (Omega J-0445, T23 saturation).  Essential facts kernel-checked: N nilpotent ·
N,Bᵢ ∈ so(η) · [Bᵢ,N]=0.  Decidable ℚ, no native_decide.
-/

namespace VGLean.S988.S988two

open Matrix

abbrev Mn := Matrix (Fin 8) (Fin 8) ℚ
abbrev Md := Matrix (Fin 16) (Fin 16) ℚ   -- independence-minor size

def eta : Mn := !![1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, -1]
def N : Mn := !![0, 1, 0, 0, 0, -1, 0, 0; -1, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, -1; 0, 0, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 0; -1, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, -1; 0, 0, -1, 0, 0, 0, 1, 0]
def B0 : Mn := !![0, 1, 0, 0, 0, -1, 0, 0; -1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]
def B1 : Mn := !![0, -1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]
def B2 : Mn := !![0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]
def B3 : Mn := !![0, 0, -1, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 1; 1, 0, 0, 0, -1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0]
def B4 : Mn := !![0, 0, 0, 1, 0, 0, 0, -1; 0, 0, -1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 0, 0; -1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 0, 0, 0]
def B5 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, -1; 0, 0, -1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0, 0, 0]
def B6 : Mn := !![0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 0; 0, -1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]
def B7 : Mn := !![0, 0, -1, 0, 0, 0, 1, 0; 0, 0, 0, -1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]
def B8 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]
def B9 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0]
def B10 : Mn := !![0, -1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]
def B11 : Mn := !![0, 0, 0, 0, 0, 0, -1, 0; 0, 0, 0, -1, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0]
def B12 : Mn := !![0, 0, 0, 0, 0, 0, 0, -1; 0, 0, 1, 0, 0, 0, -1, 0; 0, -1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 1, 0, 0, 0]
def B13 : Mn := !![0, 0, 0, 1, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, -1, 0; 0, -1, 0, 0, 0, 1, 0, 0; -1, 0, 0, 0, 0, 0, 0, 0]
def B14 : Mn := !![0, 0, -1, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, -1; 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -1; 1, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 1, 0, 0]
def B15 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, 1, 0]

def inSO (A : Mn) : Prop := Aᵀ * eta + eta * A = 0
def commN (A B : Mn) : Mn := A * B - B * A

macro "mat" : tactic =>
  `(tactic| (apply Matrix.ext; intro i j;
             fin_cases i <;> fin_cases j <;>
             simp [eta, N, B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, inSO, commN,
                   Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
                   Matrix.transpose_apply, Matrix.zero_apply, Matrix.neg_apply,
                   Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five,
                   Fin.sum_univ_six, Fin.sum_univ_seven, Fin.sum_univ_eight,
                   Fin.sum_univ_zero, Fin.sum_univ_succ] <;>
             norm_num))

-- N nilpotent (rank-4, depth 2).
theorem N_nilpotent : N * N = 0 := by mat

-- N and the centralizer basis lie in so(eta).
theorem N_inSO : inSO N := by mat
theorem B0_inSO : inSO B0 := by mat
theorem B1_inSO : inSO B1 := by mat
theorem B2_inSO : inSO B2 := by mat
theorem B3_inSO : inSO B3 := by mat
theorem B4_inSO : inSO B4 := by mat
theorem B5_inSO : inSO B5 := by mat
theorem B6_inSO : inSO B6 := by mat
theorem B7_inSO : inSO B7 := by mat
theorem B8_inSO : inSO B8 := by mat
theorem B9_inSO : inSO B9 := by mat
theorem B10_inSO : inSO B10 := by mat
theorem B11_inSO : inSO B11 := by mat
theorem B12_inSO : inSO B12 := by mat
theorem B13_inSO : inSO B13 := by mat
theorem B14_inSO : inSO B14 := by mat
theorem B15_inSO : inSO B15 := by mat

-- Centralizer law: every basis element commutes with N.
theorem B0_comm : commN B0 N = 0 := by mat
theorem B1_comm : commN B1 N = 0 := by mat
theorem B2_comm : commN B2 N = 0 := by mat
theorem B3_comm : commN B3 N = 0 := by mat
theorem B4_comm : commN B4 N = 0 := by mat
theorem B5_comm : commN B5 N = 0 := by mat
theorem B6_comm : commN B6 N = 0 := by mat
theorem B7_comm : commN B7 N = 0 := by mat
theorem B8_comm : commN B8 N = 0 := by mat
theorem B9_comm : commN B9 N = 0 := by mat
theorem B10_comm : commN B10 N = 0 := by mat
theorem B11_comm : commN B11 N = 0 := by mat
theorem B12_comm : commN B12 N = 0 := by mat
theorem B13_comm : commN B13 N = 0 := by mat
theorem B14_comm : commN B14 N = 0 := by mat
theorem B15_comm : commN B15 N = 0 := by mat

-- Linear independence of B₀..B_{15} is the probe's (Alpha's export: basis from the
-- nullspace of ad(N)|so(η), independent by construction); the dim-16 evaluation minor
-- exceeds the decidable-tactic heartbeat budget, so it is not re-checked in-kernel here
-- (honest boundary, as in A2: dimension-completeness is the probe, not Lean).

end VGLean.S988.S988two
