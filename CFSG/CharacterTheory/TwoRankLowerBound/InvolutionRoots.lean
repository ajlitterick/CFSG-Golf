module

public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicTwoSubgroups

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers


theorem commuting_involutions_eq_in_cyclic_subgroup {G : Type*} [Group G] [Finite G]
    (cyclic : Subgroup G) [IsCyclic cyclic] (left right : G)
    (hleft : left ∈ cyclic) (hright : right ∈ cyclic)
    (hleftorder : orderOf left = 2) (hrightorder : orderOf right = 2) : left = right := by
  have hrank : twoRank cyclic ≤ 1 := twoRank_le_one_of_abelian_subgroups_cyclic cyclic
    (fun subgroup _ => inferInstance)
  have hleftsuborder : orderOf (⟨left, hleft⟩ : cyclic) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans hleftorder
  have hrightsuborder : orderOf (⟨right, hright⟩ : cyclic) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans hrightorder
  have hcommute := (Subgroup.le_centralizer cyclic) hright
  have hequal := commuting_involutions_eq_of_twoRank_le_one cyclic hrank
    ⟨left, hleft⟩ ⟨right, hright⟩ hleftsuborder hrightsuborder
    (Subtype.ext (Subgroup.mem_centralizer_iff.mp hcommute left hleft))
  exact congrArg Subtype.val hequal


end CFSG.TwoRankLowerBound.Helpers
