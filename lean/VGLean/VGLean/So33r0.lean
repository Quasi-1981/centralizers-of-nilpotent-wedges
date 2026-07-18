import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.style.longLine false      -- generated wide matrix literals
set_option linter.unusedSimpArgs false       -- one `mat` tactic covers several Fin sizes


/-!
# A2 — iso 6/6 : (3,3) rank-0 wedge, FULL centralizer  c(N) ≅ (sp(2,ℝ) ⊕ so(1,1)) ⋉ h₅
Full c(N) = (sp(2,ℝ) Levi ⊕ so(1,1) boost centre) ⋉ Heisenberg h₅, inside the Jacobi 6-rep.
NB: the Levi is sp(2,ℝ) (=sl(2,ℝ), dim 3), a proper symplectic subalgebra of sp(4,ℝ).  The extra
reductive centre so(η|G) here is so(1,1) — a NON-compact boost (eigenvalues ±1), because the core
signature is (1,1); contrast So42r0 where it is compact so(2) ((2,0)).  This compact-vs-boost
split of the reductive centre is exactly the compact-Levi ⟺ q=1 signature anatomy (C1).

★SCOPE: this is the FULL centralizer c(N), dim 9 = dim c(N) (S933/S946 probe).
Structure: reductive-centre generator W (index 8) = so(1,1) boost, NON-compact (eigenvalues ±1) = so(eta|G) of the Levi; W acts on the h5 module in sp(J), commutes with the sp(2,R) Levi (distinct factors), so c(N)=(sp(2,R) (+) so(1,1)) (x) h5
What is proven in-kernel: N nilpotent · N,Bᵢ ∈ so(η) · [Bᵢ,N]=0 (⟹ B ⊂ c(N)) ·
ψ(Levi) ∈ sp(J) (construct anchor) · Bᵢ and Cᵢ each linearly independent (invertible
evaluation minor) · both bracket tables with IDENTICAL structure constants ⟹ Bᵢ ↦ Cᵢ
is a Lie isomorphism c(N) ≅ construct.  Basis-completeness (dim c(N)=9) is the probe's;
Lean re-verifies the exact identities (fourth layer).  All decidable ℚ (no native_decide).
-/

namespace VGLean.A2.So33r0

open Matrix

abbrev Mn := Matrix (Fin 6) (Fin 6) ℚ   -- core ambient so(p,q)
abbrev Mc := Matrix (Fin 6) (Fin 6) ℚ   -- construct ambient
abbrev Mp := Matrix (Fin 4) (Fin 4) ℚ   -- Levi anchor block (sp(J))
abbrev Md := Matrix (Fin 9) (Fin 9) ℚ   -- independence-minor size

def eta : Mn := !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, -1]
def Jsp : Mp := !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]
def N : Mn := !![0, 1, 0, 0, -1, 0; -1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0; -1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0]
def B0 : Mn := !![0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def B1 : Mn := !![0, 1, 0, 0, -1, 0; -1, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 1, 0; -1, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0]
def B2 : Mn := !![0, 1, 0, 0, 1, 0; -1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0; 1, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0]
def B3 : Mn := !![0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def B4 : Mn := !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, -1, 0]
def B5 : Mn := !![0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, 0; 1, 0, 0, -1, 0, 0; 0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def B6 : Mn := !![0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0; 1, 0, 0, -1, 0, 0]
def B7 : Mn := !![0, -1, 0, 0, 1, 0; 1, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 1, 0; 1, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0]
def B8 : Mn := !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, -1; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0]
def C0 : Mc := !![0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, 0]
def C1 : Mc := !![0, 0, 0, 0, 0, 0; 0, 0, 0, 2, 0, 0; 0, 0, 0, 0, -2, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def C2 : Mc := !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, -2, 0, 0, 0, 0; 0, 0, 2, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def C3 : Mc := !![0, 0, 0, 1/2, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def C4 : Mc := !![0, 0, 0, 0, 1/2, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def C5 : Mc := !![0, -1/2, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def C6 : Mc := !![0, 0, -1/2, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0]
def C7 : Mc := !![0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def C8 : Mc := !![0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0; 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0]
def psi0 : Mp := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
def psi1 : Mp := !![0, 0, 2, 0; 0, 0, 0, -2; 0, 0, 0, 0; 0, 0, 0, 0]
def psi2 : Mp := !![0, 0, 0, 0; 0, 0, 0, 0; -2, 0, 0, 0; 0, 2, 0, 0]
def minorB : Md := !![0, 1, 1, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, -1, 0, 0, 0; -1, 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, -1, 1, 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1]
def minorBinv : Md := !![0, 0, -1, 0, 0, 0, 0, 0, 0; 1/2, 0, 0, 0, 0, 0, -1/2, 0, 0; 1/2, 0, 0, 1/2, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1, 0; 0, -1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1/2, 0, 0, -1/2, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1]
def minorC : Md := !![0, 0, 0, 0, 0, -1/2, 0, 0, 0; 0, 0, 0, 0, 0, 0, -1/2, 0, 0; 0, 0, 0, 1/2, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1/2, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 0, 0; 0, 0, -2, 0, 0, 0, 0, 0, 0]
def minorCinv : Md := !![0, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1/2, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1/2; 0, 0, 2, 0, 0, 0, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 0, 0; -2, 0, 0, 0, 0, 0, 0, 0, 0; 0, -2, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0, 0]

def inSOn (A : Mn) : Prop := Aᵀ * eta + eta * A = 0
def inSPp (A : Mp) : Prop := Aᵀ * Jsp + Jsp * A = 0
def commN (A B : Mn) : Mn := A * B - B * A
def commC (A B : Mc) : Mc := A * B - B * A

macro "mat" : tactic =>
  `(tactic| (apply Matrix.ext; intro i j;
             fin_cases i <;> fin_cases j <;>
             simp [eta, N, B0, B1, B2, B3, B4, B5, B6, B7, B8, C0, C1, C2, C3, C4, C5, C6, C7, C8, Jsp, psi0, psi1, psi2, minorB, minorBinv, minorC, minorCinv,
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
theorem B6_inSO : inSOn B6 := by mat
theorem B7_inSO : inSOn B7 := by mat
theorem B8_inSO : inSOn B8 := by mat

-- Centralizer law: every basis element commutes with N  (⟹ B ⊂ c(N)).
theorem B0_comm : commN B0 N = 0 := by mat
theorem B1_comm : commN B1 N = 0 := by mat
theorem B2_comm : commN B2 N = 0 := by mat
theorem B3_comm : commN B3 N = 0 := by mat
theorem B4_comm : commN B4 N = 0 := by mat
theorem B5_comm : commN B5 N = 0 := by mat
theorem B6_comm : commN B6 N = 0 := by mat
theorem B7_comm : commN B7 N = 0 := by mat
theorem B8_comm : commN B8 N = 0 := by mat

-- Construct anchor: the Levi images ψ(Lᵢ) lie in sp(J).
theorem psi0_anchor : inSPp psi0 := by mat
theorem psi1_anchor : inSPp psi1 := by mat
theorem psi2_anchor : inSPp psi2 := by mat

-- Linear independence (decidable certificate): the evaluation minor is invertible.
-- minorB[k][l] = (Bₗ) at probe coord k; minorB·minorBinv = 1 ⟹ B₀..B_{d-1} independent.
theorem B_indep : minorB * minorBinv = 1 := by mat
theorem C_indep : minorC * minorCinv = 1 := by mat

-- Bracket table of the CORE basis B (closes with the measured structure constants).
theorem brB_0_1 : commN B0 B1 = (2:ℚ) • B1 := by mat
theorem brB_0_2 : commN B0 B2 = (-2:ℚ) • B2 := by mat
theorem brB_0_3 : commN B0 B3 = B3 := by mat
theorem brB_0_4 : commN B0 B4 = B4 := by mat
theorem brB_0_5 : commN B0 B5 = -B5 := by mat
theorem brB_0_6 : commN B0 B6 = -B6 := by mat
theorem brB_0_7 : commN B0 B7 = 0 := by mat
theorem brB_0_8 : commN B0 B8 = 0 := by mat
theorem brB_1_2 : commN B1 B2 = (-4:ℚ) • B0 := by mat
theorem brB_1_3 : commN B1 B3 = 0 := by mat
theorem brB_1_4 : commN B1 B4 = 0 := by mat
theorem brB_1_5 : commN B1 B5 = (2:ℚ) • B3 := by mat
theorem brB_1_6 : commN B1 B6 = (-2:ℚ) • B4 := by mat
theorem brB_1_7 : commN B1 B7 = 0 := by mat
theorem brB_1_8 : commN B1 B8 = 0 := by mat
theorem brB_2_3 : commN B2 B3 = (-2:ℚ) • B5 := by mat
theorem brB_2_4 : commN B2 B4 = (2:ℚ) • B6 := by mat
theorem brB_2_5 : commN B2 B5 = 0 := by mat
theorem brB_2_6 : commN B2 B6 = 0 := by mat
theorem brB_2_7 : commN B2 B7 = 0 := by mat
theorem brB_2_8 : commN B2 B8 = 0 := by mat
theorem brB_3_4 : commN B3 B4 = 0 := by mat
theorem brB_3_5 : commN B3 B5 = B7 := by mat
theorem brB_3_6 : commN B3 B6 = 0 := by mat
theorem brB_3_7 : commN B3 B7 = 0 := by mat
theorem brB_3_8 : commN B3 B8 = -B4 := by mat
theorem brB_4_5 : commN B4 B5 = 0 := by mat
theorem brB_4_6 : commN B4 B6 = B7 := by mat
theorem brB_4_7 : commN B4 B7 = 0 := by mat
theorem brB_4_8 : commN B4 B8 = -B3 := by mat
theorem brB_5_6 : commN B5 B6 = 0 := by mat
theorem brB_5_7 : commN B5 B7 = 0 := by mat
theorem brB_5_8 : commN B5 B8 = B6 := by mat
theorem brB_6_7 : commN B6 B7 = 0 := by mat
theorem brB_6_8 : commN B6 B8 = B5 := by mat
theorem brB_7_8 : commN B7 B8 = 0 := by mat

-- Bracket table of the CONSTRUCT basis C — IDENTICAL structure constants ⟹ Bᵢ ↦ Cᵢ is the iso.
theorem brC_0_1 : commC C0 C1 = (2:ℚ) • C1 := by mat
theorem brC_0_2 : commC C0 C2 = (-2:ℚ) • C2 := by mat
theorem brC_0_3 : commC C0 C3 = C3 := by mat
theorem brC_0_4 : commC C0 C4 = C4 := by mat
theorem brC_0_5 : commC C0 C5 = -C5 := by mat
theorem brC_0_6 : commC C0 C6 = -C6 := by mat
theorem brC_0_7 : commC C0 C7 = 0 := by mat
theorem brC_0_8 : commC C0 C8 = 0 := by mat
theorem brC_1_2 : commC C1 C2 = (-4:ℚ) • C0 := by mat
theorem brC_1_3 : commC C1 C3 = 0 := by mat
theorem brC_1_4 : commC C1 C4 = 0 := by mat
theorem brC_1_5 : commC C1 C5 = (2:ℚ) • C3 := by mat
theorem brC_1_6 : commC C1 C6 = (-2:ℚ) • C4 := by mat
theorem brC_1_7 : commC C1 C7 = 0 := by mat
theorem brC_1_8 : commC C1 C8 = 0 := by mat
theorem brC_2_3 : commC C2 C3 = (-2:ℚ) • C5 := by mat
theorem brC_2_4 : commC C2 C4 = (2:ℚ) • C6 := by mat
theorem brC_2_5 : commC C2 C5 = 0 := by mat
theorem brC_2_6 : commC C2 C6 = 0 := by mat
theorem brC_2_7 : commC C2 C7 = 0 := by mat
theorem brC_2_8 : commC C2 C8 = 0 := by mat
theorem brC_3_4 : commC C3 C4 = 0 := by mat
theorem brC_3_5 : commC C3 C5 = C7 := by mat
theorem brC_3_6 : commC C3 C6 = 0 := by mat
theorem brC_3_7 : commC C3 C7 = 0 := by mat
theorem brC_3_8 : commC C3 C8 = -C4 := by mat
theorem brC_4_5 : commC C4 C5 = 0 := by mat
theorem brC_4_6 : commC C4 C6 = C7 := by mat
theorem brC_4_7 : commC C4 C7 = 0 := by mat
theorem brC_4_8 : commC C4 C8 = -C3 := by mat
theorem brC_5_6 : commC C5 C6 = 0 := by mat
theorem brC_5_7 : commC C5 C7 = 0 := by mat
theorem brC_5_8 : commC C5 C8 = C6 := by mat
theorem brC_6_7 : commC C6 C7 = 0 := by mat
theorem brC_6_8 : commC C6 C8 = C5 := by mat
theorem brC_7_8 : commC C7 C8 = 0 := by mat

-- Reductive-centre signature (named, kernel-checked): B8³ = B8 ⟹ minimal poly x(x²−1)
-- ⟹ nonzero eigenvalues ±1 ⟹ so(η|G) = NON-compact so(1,1) boost.  (NB B8² is NOT ±1 on the full space —
--  only on its 2-plane; B8³=B8 is the clean full-matrix invariant of the eigenvalue type.)
theorem B8_cube : B8 * B8 * B8 = B8 := by mat

end VGLean.A2.So33r0
