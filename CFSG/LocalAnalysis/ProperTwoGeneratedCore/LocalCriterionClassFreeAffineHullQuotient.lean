module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullConjugacy

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G T A : Type*} [Group G] [Group T] [Group A]

theorem image_isSolvable_of_kernel_le (chi : G →* A) (rho : G →* T)
    [Group.IsSolvable chi.range] (hker : chi.ker ≤ rho.ker) :
    Group.IsSolvable rho.range := by
  let e := QuotientGroup.quotientKerEquivRange chi
  let : Group.IsSolvable (G ⧸ chi.ker) :=
    Group.isSolvable_of_isSolvable_injective e.injective
  have hk : chi.ker ≤ rho.rangeRestrict.ker := by
    intro g hg
    exact Subtype.ext (hker hg)
  exact Group.isSolvable_of_surjective
    (QuotientGroup.lift_surjective_of_surjective chi.ker
      rho.rangeRestrict rho.rangeRestrict_surjective hk)


end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
