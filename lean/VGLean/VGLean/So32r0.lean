import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.style.longLine false      -- generated wide matrix literals
set_option linter.unusedSimpArgs false       -- one `mat` tactic covers several Fin sizes


/-!
# A2 — iso 4/6 : (3,2) rank-0 wedge, FULL centralizer  c(N) ≅ sp(2,ℝ) ⋉ h₃
Full c(N) = Jacobi algebra sp(2,ℝ)⋉h₃ (here perfect core = full: so(η|G)=so(1)=0, no gap).
Jacobi faithful 4-rep.  [sp(2,ℝ) ≅ sl(2,ℝ) ≅ so(2,1); symplectic name in the sp(J) context.]

★SCOPE: this is the FULL centralizer c(N), dim 6 = dim c(N) (S933/S946 probe).
Structure: none (full c(N) = perfect core = Levi (x) h3)
What is proven in-kernel: N nilpotent · N,Bᵢ ∈ so(η) · [Bᵢ,N]=0 (⟹ B ⊂ c(N)) ·
ψ(Levi) ∈ sp(J) (construct anchor) · Bᵢ and Cᵢ each linearly independent (invertible
evaluation minor) · both bracket tables with IDENTICAL structure constants ⟹ Bᵢ ↦ Cᵢ
is a Lie isomorphism c(N) ≅ construct.  Basis-completeness (dim c(N)=6) is the probe's;
Lean re-verifies the exact identities (fourth layer).  All decidable ℚ (no native_decide).
-/

namespace VGLean.A2.So32r0

open Matrix

abbrev Mn := Matrix (Fin 5) (Fin 5) ℚ   -- core ambient so(p,q)
abbrev Mc := Matrix (Fin 4) (Fin 4) ℚ   -- construct ambient
abbrev Mp := Matrix (Fin 2) (Fin 2) ℚ   -- Levi anchor block (sp(J))
abbrev Md := Matrix (Fin 6) (Fin 6) ℚ   -- independence-minor size

def eta : Mn := !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, -1]
def Jsp : Mp := !![0, 1; -1, 0]
def N : Mn := !![0, 1, 0, 0, -1; -1, 0, 0, 1, 0; 0, 0, 0, 0, 0; 0, 1, 0, 0, -1; -1, 0, 0, 1, 0]
def B0 : Mn := !![0, 1/2, 0, 0, -1/2; -1/2, 0, 0, -1/2, 0; 0, 0, 0, 0, 0; 0, -1/2, 0, 0, 1/2; -1/2, 0, 0, -1/2, 0]
def B1 : Mn := !![0, -1/2, 0, 0, -1/2; 1/2, 0, 0, -1/2, 0; 0, 0, 0, 0, 0; 0, -1/2, 0, 0, -1/2; -1/2, 0, 0, 1/2, 0]
def B2 : Mn := !![0, 0, 0, 1, 0; 0, 0, 0, 0, -1; 0, 0, 0, 0, 0; 1, 0, 0, 0, 0; 0, -1, 0, 0, 0]
def B3 : Mn := !![0, 0, -1, 0, 0; 0, 0, 0, 0, 0; 1, 0, 0, -1, 0; 0, 0, -1, 0, 0; 0, 0, 0, 0, 0]
def B4 : Mn := !![0, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, -1, 0, 0, 1; 0, 0, 0, 0, 0; 0, 0, 1, 0, 0]
def B5 : Mn := !![0, 1, 0, 0, -1; -1, 0, 0, 1, 0; 0, 0, 0, 0, 0; 0, 1, 0, 0, -1; -1, 0, 0, 1, 0]
def C0 : Mc := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0]
def C1 : Mc := !![0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0]
def C2 : Mc := !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 0]
def C3 : Mc := !![0, 0, 1/2, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]
def C4 : Mc := !![0, -1/2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0]
def C5 : Mc := !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
def psi0 : Mp := !![0, 0; 1, 0]
def psi1 : Mp := !![0, 1; 0, 0]
def psi2 : Mp := !![1, 0; 0, -1]
def minorB : Md := !![1/2, -1/2, 0, 0, 0, 1; 0, 0, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0; -1/2, -1/2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0; -1/2, -1/2, 0, 0, 0, 1]
def minorBinv : Md := !![1, 0, 0, 0, 0, -1; -1, 0, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0; 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, -1/2, 0, 1/2]
def minorC : Md := !![0, 0, 0, 0, -1/2, 0; 0, 0, 0, 1/2, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0]
def minorCinv : Md := !![0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0; 0, 2, 0, 0, 0, 0; -2, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0]

def inSOn (A : Mn) : Prop := Aᵀ * eta + eta * A = 0
def inSPp (A : Mp) : Prop := Aᵀ * Jsp + Jsp * A = 0
def commN (A B : Mn) : Mn := A * B - B * A
def commC (A B : Mc) : Mc := A * B - B * A

macro "mat" : tactic =>
  `(tactic| (apply Matrix.ext; intro i j;
             fin_cases i <;> fin_cases j <;>
             simp [eta, N, B0, B1, B2, B3, B4, B5, C0, C1, C2, C3, C4, C5, Jsp, psi0, psi1, psi2, minorB, minorBinv, minorC, minorCinv,
                   inSOn, inSPp, commN, commC,
                   Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
                   Matrix.transpose_apply, Matrix.smul_apply, Matrix.zero_apply,
                   Matrix.neg_apply, Fin.sum_univ_one, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
                   Fin.sum_univ_five, Fin.sum_univ_six, Fin.sum_univ_seven,
                   Fin.sum_univ_eight, Fin.sum_univ_zero, Fin.sum_univ_succ] <;>
             norm_num))

-- N nilpotent: N^2 = 0.
theorem N_nilpotent : N * N = 0 := by mat

-- Core-adapted basis of the FULL centralizer lies in so(η).
theorem N_inSO : inSOn N := by mat
theorem B0_inSO : inSOn B0 := by mat
theorem B1_inSO : inSOn B1 := by mat
theorem B2_inSO : inSOn B2 := by mat
theorem B3_inSO : inSOn B3 := by mat
theorem B4_inSO : inSOn B4 := by mat
theorem B5_inSO : inSOn B5 := by mat

-- Centralizer law: every basis element commutes with N  (⟹ B ⊂ c(N)).
theorem B0_comm : commN B0 N = 0 := by mat
theorem B1_comm : commN B1 N = 0 := by mat
theorem B2_comm : commN B2 N = 0 := by mat
theorem B3_comm : commN B3 N = 0 := by mat
theorem B4_comm : commN B4 N = 0 := by mat
theorem B5_comm : commN B5 N = 0 := by mat

-- Construct anchor: the Levi images ψ(Lᵢ) lie in sp(J).
theorem psi0_anchor : inSPp psi0 := by mat
theorem psi1_anchor : inSPp psi1 := by mat
theorem psi2_anchor : inSPp psi2 := by mat

-- Linear independence (decidable certificate): the evaluation minor is invertible.
-- minorB[k][l] = (Bₗ) at probe coord k; minorB·minorBinv = 1 ⟹ B₀..B_{d-1} independent.
theorem B_indep : minorB * minorBinv = 1 := by mat
theorem C_indep : minorC * minorCinv = 1 := by mat

-- Bracket table of the CORE basis B (closes with the measured structure constants).
theorem brB_0_1 : commN B0 B1 = -B2 := by mat
theorem brB_0_2 : commN B0 B2 = (2:ℚ) • B0 := by mat
theorem brB_0_3 : commN B0 B3 = B4 := by mat
theorem brB_0_4 : commN B0 B4 = 0 := by mat
theorem brB_0_5 : commN B0 B5 = 0 := by mat
theorem brB_1_2 : commN B1 B2 = (-2:ℚ) • B1 := by mat
theorem brB_1_3 : commN B1 B3 = 0 := by mat
theorem brB_1_4 : commN B1 B4 = B3 := by mat
theorem brB_1_5 : commN B1 B5 = 0 := by mat
theorem brB_2_3 : commN B2 B3 = B3 := by mat
theorem brB_2_4 : commN B2 B4 = -B4 := by mat
theorem brB_2_5 : commN B2 B5 = 0 := by mat
theorem brB_3_4 : commN B3 B4 = B5 := by mat
theorem brB_3_5 : commN B3 B5 = 0 := by mat
theorem brB_4_5 : commN B4 B5 = 0 := by mat

-- Bracket table of the CONSTRUCT basis C — IDENTICAL structure constants ⟹ Bᵢ ↦ Cᵢ is the iso.
theorem brC_0_1 : commC C0 C1 = -C2 := by mat
theorem brC_0_2 : commC C0 C2 = (2:ℚ) • C0 := by mat
theorem brC_0_3 : commC C0 C3 = C4 := by mat
theorem brC_0_4 : commC C0 C4 = 0 := by mat
theorem brC_0_5 : commC C0 C5 = 0 := by mat
theorem brC_1_2 : commC C1 C2 = (-2:ℚ) • C1 := by mat
theorem brC_1_3 : commC C1 C3 = 0 := by mat
theorem brC_1_4 : commC C1 C4 = C3 := by mat
theorem brC_1_5 : commC C1 C5 = 0 := by mat
theorem brC_2_3 : commC C2 C3 = C3 := by mat
theorem brC_2_4 : commC C2 C4 = -C4 := by mat
theorem brC_2_5 : commC C2 C5 = 0 := by mat
theorem brC_3_4 : commC C3 C4 = C5 := by mat
theorem brC_3_5 : commC C3 C5 = 0 := by mat
theorem brC_4_5 : commC C4 C5 = 0 := by mat

end VGLean.A2.So32r0
