import Mathlib.Algebra.Lie.Classical

set_option linter.style.header false

/-!
# A0 hello-so(p,q) — toolchain smoke test

Confirms the pinned mathlib (v4.32.0) exposes the indefinite orthogonal Lie
algebra `so' p q R` from `Mathlib.Algebra.Lie.Classical`, and that we can name
`so'(2,2)` over `ℚ` — the ambient of the W33 nilpotent-wedge centralizers
(Т17/Т18 §12).  Nothing is proved here; this is the A0 gate: *the object exists
and the imports compile against the pinned toolchain.*
-/

open LieAlgebra Orthogonal

-- The indefinite orthogonal Lie algebra exists as a mathlib definition.
#check @LieAlgebra.Orthogonal.so'

/-- `so'(2,2)` over `ℚ`: skew-adjoint matrices for the indefinite diagonal
`diag(1,1,-1,-1)`.  Ambient of the smallest wedge centralizer targeted in A1
(the `(2,2)` rank-0 core = bare `so(2,1)`).  Type left to inference so the
matrix `LieRing` instance is taken from `so'` itself. -/
abbrev so22 := LieAlgebra.Orthogonal.so' (Fin 2) (Fin 2) ℚ

#check so22

-- The subalgebra carries a genuine Lie algebra structure over ℚ.
example : LieAlgebra ℚ so22 := inferInstance
