module

public import CFSG.ClassicalInvolution.Q3.Q3NSShape
public import CFSG.ClassicalInvolution.Q3.Q3NLFrame
import CFSG.ClassicalInvolution.Asc77.WP3SCUTq

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups commutatorElement

section Sylow

variable {G : Type} [Group G]


end Sylow

section ConjImage

variable {G : Type} [Group G]


end ConjImage

section Statements


end Statements

section Frame3


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem isPGroup_zpowers_of_sq_eq_one3 {c : G} (hc : c * c = 1) :
    IsPGroup 2 (Subgroup.zpowers c) := by
  refine isPGroup_two_of_sq_eq_one fun x hx => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← (Commute.refl c).mul_zpow, hc, one_zpow]


end Frame3

end CFSG.ClassicalInvolution.Q3.Q3NS
