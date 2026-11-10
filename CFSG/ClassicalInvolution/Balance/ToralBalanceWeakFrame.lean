module

public import CFSG.ClassicalInvolution.Balance.ToralBalanceFrame
public import CFSG.ClassicalInvolution.Balance.WeakFrame.TwoBalanced
import CFSG.ClassicalInvolution.PerfectCase.Basic

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

theorem IsInvolutionMember.of_weakMember {F : Type*} [Field F] [Finite F] {G : Type*} [Group G]
    {K : Subgroup G} {z : G} (h : WeakMember F K z) (h4 : 4 ≤ Nat.card F) :
    IsInvolutionMember K := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have hc := h.isCentralInvolution
  exact ⟨h.perfect.commutator_eq_top,
    Components.quasisimple_of_equiv e (isQuasisimple_specialLinearGroup_two h4), z, hc.mem, hc.sq,
    hc.central, h.subnormal⟩

section WeakFrame


end WeakFrame

end CFSG.ClassicalInvolution.Balance
