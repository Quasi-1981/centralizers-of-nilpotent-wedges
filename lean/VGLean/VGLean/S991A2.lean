import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000   -- dense 9×9 / 10×10 so(5,q) entrywise checks

/-!
# S991 leg-2 — so(5,5) two-wedge rank-4, the ★Λ²-COCYCLE (n=10, T24 candidate) [MAIN]
Alpha's export S991 (B-visa J-0447).  Module = W⊗G (dv=8), centre = Λ²W (dim 6); the cocycle
[u⊗a,v⊗b] = (u∧v)·η'(a,b) is kernel-checked as OBSERVED structure constants (Alpha's leg-3
boundary: the two-block split is a choice, cross-block vanishing a raw fact, not an invariant).
-/

namespace VGLean.S991.S991A2

open Matrix

abbrev Mn := Matrix (Fin 10) (Fin 10) ℚ

def eta : Mn := !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]
def N : Mn := !![0, 1, 0, 0, 0, 0, -1, 0, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1, 0; 0, 0, -1, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 0, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1, 0; 0, 0, -1, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def MB0 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 0, 0, 0]
def MB1 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]
def MB2 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, -1; 0, 0, 0, -1, 0, 0, 0, 0, 1, 0]
def MB3 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, -1, 0, 0]
def MB4 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def MB5 : Mn := !![0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def MB6 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def MB7 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Z0 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Z1 : Mn := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, -1, 0, 0; 0, -1, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, -1, 0, 0; 0, -1, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Z2 : Mn := !![0, 0, 0, 1, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Z3 : Mn := !![0, 0, -1, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Z4 : Mn := !![0, 1, 0, 0, 0, 0, -1, 0, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 0, 0, 0; -1, 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Z5 : Mn := !![0, -1, 0, 0, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def inSO (A : Mn) : Prop := Aᵀ * eta + eta * A = 0
def commN (A B : Mn) : Mn := A * B - B * A

macro "mat" : tactic =>
  `(tactic| (apply Matrix.ext; intro i j;
             fin_cases i <;> fin_cases j <;>
             simp [eta, N, MB0, MB1, MB2, MB3, MB4, MB5, MB6, MB7, Z0, Z1, Z2, Z3, Z4, Z5, inSO, commN,
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
theorem MB4_inSO : inSO MB4 := by mat
theorem MB5_inSO : inSO MB5 := by mat
theorem MB6_inSO : inSO MB6 := by mat
theorem MB7_inSO : inSO MB7 := by mat
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
theorem MB4_comm : commN MB4 N = 0 := by mat
theorem MB5_comm : commN MB5 N = 0 := by mat
theorem MB6_comm : commN MB6 N = 0 := by mat
theorem MB7_comm : commN MB7 N = 0 := by mat

-- ★Λ²-COCYCLE (observed structure constants in THIS block-adapted basis — NOT claimed an
--  invariant; the multiplicity-2 two-block split is a choice, cross-block vanishing a raw
--  fact, cf. Alpha's leg-3 named-question).  [MBₐ,MB_b] = Σ cₖ·Zₖ = the Λ²W cocycle.
theorem cocyc_0_1 : commN MB0 MB1 = Z5 := by mat
theorem cocyc_0_2 : commN MB0 MB2 = Z0 := by mat
theorem cocyc_0_3 : commN MB0 MB3 = Z1 := by mat
theorem cocyc_1_2 : commN MB1 MB2 = -Z2 := by mat
theorem cocyc_1_3 : commN MB1 MB3 = -Z3 := by mat
theorem cocyc_2_3 : commN MB2 MB3 = -Z4 - Z5 := by mat
theorem cocyc_0_4 : commN MB0 MB4 = 0 := by mat
theorem cocyc_0_5 : commN MB0 MB5 = 0 := by mat
theorem cocyc_0_6 : commN MB0 MB6 = 0 := by mat
theorem cocyc_0_7 : commN MB0 MB7 = 0 := by mat
theorem cocyc_1_4 : commN MB1 MB4 = 0 := by mat
theorem cocyc_1_5 : commN MB1 MB5 = 0 := by mat
theorem cocyc_1_6 : commN MB1 MB6 = 0 := by mat
theorem cocyc_1_7 : commN MB1 MB7 = 0 := by mat
theorem cocyc_2_4 : commN MB2 MB4 = 0 := by mat
theorem cocyc_2_5 : commN MB2 MB5 = 0 := by mat
theorem cocyc_2_6 : commN MB2 MB6 = 0 := by mat
theorem cocyc_2_7 : commN MB2 MB7 = 0 := by mat
theorem cocyc_3_4 : commN MB3 MB4 = 0 := by mat
theorem cocyc_3_5 : commN MB3 MB5 = 0 := by mat
theorem cocyc_3_6 : commN MB3 MB6 = 0 := by mat
theorem cocyc_3_7 : commN MB3 MB7 = 0 := by mat
theorem cocyc_4_5 : commN MB4 MB5 = -Z5 := by mat
theorem cocyc_4_6 : commN MB4 MB6 = -Z0 := by mat
theorem cocyc_4_7 : commN MB4 MB7 = -Z1 := by mat
theorem cocyc_5_6 : commN MB5 MB6 = Z2 := by mat
theorem cocyc_5_7 : commN MB5 MB7 = Z3 := by mat
theorem cocyc_6_7 : commN MB6 MB7 = Z4 + Z5 := by mat

end VGLean.S991.S991A2
