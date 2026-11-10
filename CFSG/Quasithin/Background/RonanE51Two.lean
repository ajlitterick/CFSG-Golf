module

public import CFSG.Quasithin.Background.RonanE51Basic

public section

namespace CFSG.Quasithin.RonanE51

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_twoResidual {S : Subgroup G}
    (h : Group.IsSolvable ↥(twoResidual S)) : Group.IsSolvable ↥S := by
  have hOS : twoResidual S ≤ S := twoResidual_le S
  have hNn : ((twoResidual S).subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOS).2 (le_normalizer_twoResidual S)
  have hNs : Group.IsSolvable ↥((twoResidual S).subgroupOf S) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hOS).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hOS).injective
  refine isSolvable_of_forall_pow_mem hNs fun y => ?_
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient S (y : G) y.2
  exact ⟨k, hk⟩


end CFSG.Quasithin.RonanE51
