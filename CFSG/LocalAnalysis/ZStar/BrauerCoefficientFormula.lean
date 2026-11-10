module

public import CFSG.LocalAnalysis.ZStar.BrauerBlockLift

public section

namespace CFSG

namespace ZStar.BrauerCoefficientFormula

open ZStar.Helpers

universe u

noncomputable section

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H


theorem orderOf_conj_eq (x y : G) :
    orderOf (x * y * x⁻¹) = orderOf y := by
  have hsemi : SemiconjBy x y (x * y * x⁻¹) := by
    show x * y = (x * y * x⁻¹) * x
    group
  exact (SemiconjBy.orderOf_eq x hsemi).symm


end

end ZStar.BrauerCoefficientFormula

end CFSG
