import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000   -- dense 9×9 / 10×10 so(5,q) entrywise checks

/-!
# S991 leg-2 — so(5,4) two-wedge rank-4 saturating (n=9): module + Λ²-cocycle (small de-risk)
Alpha's export S991 (B-visa J-0447).  Kernel-checks the module facts + the observed cocycle.
-/

namespace VGLean.S991.S991A1

open Matrix

abbrev Mn := Matrix (Fin 9) (Fin 9) ℚ

def eta : Mn := !![1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1]
def N : Mn := !![0, 1, 0, 0, 0, 0, -1, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1; 0, 0, -1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1; 0, 0, -1, 0, 0, 0, 0, 1, 0]
def MB0 : Mn := !![0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0]
def MB1 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0]
def MB2 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0]
def MB3 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0, 0]
def Z0 : Mn := !![0, 1, 0, 0, 0, 0, -1, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Z1 : Mn := !![0, 0, 1, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Z2 : Mn := !![0, 0, 0, 1, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0]
def Z3 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, -1, 0; 0, -1, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, -1, 0; 0, -1, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Z4 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 1, 0, 0]
def Z5 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1; 0, 0, -1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1; 0, 0, -1, 0, 0, 0, 0, 1, 0]

def inSO (A : Mn) : Prop := Aᵀ * eta + eta * A = 0
def commN (A B : Mn) : Mn := A * B - B * A

macro "mat" : tactic =>
  `(tactic| (apply Matrix.ext; intro i j;
             fin_cases i <;> fin_cases j <;>
             simp [eta, N, MB0, MB1, MB2, MB3, Z0, Z1, Z2, Z3, Z4, Z5, inSO, commN,
                   Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
                   Matrix.transpose_apply, Matrix.zero_apply, Matrix.neg_apply,
                   Matrix.smul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five,
                   Fin.sum_univ_six, Fin.sum_univ_seven, Fin.sum_univ_eight,
                   Fin.sum_univ_zero, Fin.sum_univ_succ] <;>
             norm_num))

-- N nilpotent (rank-4, depth 2).
theorem N_nilpotent : N * N = 0 := by mat

theorem N_inSO : inSO N := by mat
theorem MB0_inSO : inSO MB0 := by mat
theorem MB1_inSO : inSO MB1 := by mat
theorem MB2_inSO : inSO MB2 := by mat
theorem MB3_inSO : inSO MB3 := by mat
theorem Z0_inSO : inSO Z0 := by mat
theorem Z1_inSO : inSO Z1 := by mat
theorem Z2_inSO : inSO Z2 := by mat
theorem Z3_inSO : inSO Z3 := by mat
theorem Z4_inSO : inSO Z4 := by mat
theorem Z5_inSO : inSO Z5 := by mat

-- Module centralizes N: [MBᵢ,N]=0.
theorem MB0_comm : commN MB0 N = 0 := by mat
theorem MB1_comm : commN MB1 N = 0 := by mat
theorem MB2_comm : commN MB2 N = 0 := by mat
theorem MB3_comm : commN MB3 N = 0 := by mat

-- ★Λ²-COCYCLE (observed structure constants in THIS block-adapted basis — NOT claimed an
--  invariant; the multiplicity-2 two-block split is a choice, cross-block vanishing a raw
--  fact, cf. Alpha's leg-3 named-question).  [MBₐ,MB_b] = Σ cₖ·Zₖ = the Λ²W cocycle.
theorem cocyc_0_1 : commN MB0 MB1 = -Z0 := by mat
theorem cocyc_0_2 : commN MB0 MB2 = -Z1 := by mat
theorem cocyc_0_3 : commN MB0 MB3 = -Z2 := by mat
theorem cocyc_1_2 : commN MB1 MB2 = -Z3 := by mat
theorem cocyc_1_3 : commN MB1 MB3 = -Z4 := by mat
theorem cocyc_2_3 : commN MB2 MB3 = -Z5 := by mat

end VGLean.S991.S991A1
