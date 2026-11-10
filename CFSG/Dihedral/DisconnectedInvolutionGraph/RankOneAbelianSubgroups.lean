module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneAbelianTwo

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_abelian_subgroup_cyclic (hpgroup : IsPGroup 2 G)
    (hrank : NoCommutingDistinctInvolutions G) (subgroup : Subgroup G)
    (hcommute : ∀ first second : subgroup, first * second = second * first) :
    IsCyclic subgroup := by
  let _ : CommGroup subgroup := { (inferInstance : Group subgroup) with mul_comm := hcommute }
  exact rank_one_abelian_two_group_cyclic subgroup (hpgroup.to_subgroup subgroup)
    (subgroup_no_commuting_distinct_involutions subgroup hrank)


end CFSG.DisconnectedInvolutionGraph.Helpers
