module

public import CFSG.Monster.B.Dyadic.FixedLine

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Dyadic

open Module
open scoped Matrix

section Generic

variable {K : Type*} [Field K] {n : ℕ}

theorem finrank_ker_add_rank (A : Matrix (Fin n) (Fin n) K) :
    finrank K (LinearMap.ker A.mulVecLin) + A.rank = n := by
  rw [Matrix.rank, add_comm, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]


end Generic

section Ring


end Ring


end CFSG.Monster.B.Dyadic
