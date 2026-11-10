module

public import CFSG.Assembly.OrderReductions.OddKernelInvolutions
public import CFSG.Assembly.OrderReductions.Reduction
public import CFSG.Assembly.OrderReductions.CyclicTwoTransfer

public section

namespace CFSG.OrderReductions.RankOneInduction

universe group_universe

open CFSG.OrderReductions.InvolutionGraph

@[expose] def NoFourInvolutions (group : Type*) [Group group] : Prop :=
  ∀ first second : Involution group, Commute first.val second.val → first = second


theorem noFourInvolutions_quotient {group : Type*} [Group group] [Finite group]
    (no_four : NoFourInvolutions group) (normal : Subgroup group) [normal.Normal]
    (odd_normal : Odd (Nat.card normal)) : NoFourInvolutions (group ⧸ normal) := by
  apply CFSG.OrderReductions.OddKernelInvolutions.quotient_no_four_involutions
    (QuotientGroup.mk' normal) (QuotientGroup.mk'_surjective normal) _ no_four
  rw [QuotientGroup.ker_mk']
  exact odd_normal


theorem involution_image_central_of_coreFree_centrality
    (centrality : ∀ (group : Type group_universe) [Group group] [Finite group],
      NoFourInvolutions group → CFSG.OrderReductions.OddCore.oddCore group = ⊥ →
      ∀ involution : Involution group, involution.val ∈ Subgroup.center group)
    (group : Type group_universe) [Group group] [Finite group] (no_four : NoFourInvolutions group)
    (involution : Involution group) :
    QuotientGroup.mk' (CFSG.OrderReductions.OddCore.oddCore group) involution.val ∈
      Subgroup.center (group ⧸ CFSG.OrderReductions.OddCore.oddCore group) := by
  let projection := QuotientGroup.mk' (CFSG.OrderReductions.OddCore.oddCore group)
  have kernel_odd : Odd (Nat.card projection.ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.OrderReductions.OddCore.oddCore_odd group
  let image : Involution (group ⧸ CFSG.OrderReductions.OddCore.oddCore group) :=
    ⟨projection involution.val,
      CFSG.OrderReductions.OddKernelInvolutions.involution_image_order projection kernel_odd involution⟩
  exact centrality _
    (noFourInvolutions_quotient no_four _ (CFSG.OrderReductions.OddCore.oddCore_odd group))
    (CFSG.OrderReductions.OddCore.oddCore_quotient_eq_bot group) image

end CFSG.OrderReductions.RankOneInduction
