module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionGraph
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicPSubgroupOrder

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]


theorem cyclic_overgroup_equal_card_subgroups [Finite G] (cyclic : Subgroup G) [IsCyclic cyclic]
    (first second : Subgroup G) (hfirst : first ≤ cyclic) (hsecond : second ≤ cyclic)
    (hcard : Nat.card first = Nat.card second) : first = second := by
  have hfirstCard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hfirst).toEquiv
  have hsecondCard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsecond).toEquiv
  have hrelative : first.subgroupOf cyclic = second.subgroupOf cyclic := by
    have hequal := hfirstCard.trans (hcard.trans hsecondCard.symm)
    apply le_antisymm
    · exact cyclic_subgroup_le_of_card_dvd _ _ (hequal ▸ dvd_refl _)
    · exact cyclic_subgroup_le_of_card_dvd _ _ (hequal.symm ▸ dvd_refl _)
  have hinter := Subgroup.subgroupOf_inj.mp hrelative
  simpa only [inf_eq_left.mpr hfirst, inf_eq_left.mpr hsecond] using hinter


end CFSG.DisconnectedInvolutionGraph.Helpers
