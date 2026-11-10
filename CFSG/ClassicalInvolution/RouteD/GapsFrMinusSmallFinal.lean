module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusFinal
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallPattern

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwinTDSmallPattern7 (p f : ℕ) [Fact p.Prime] : Prop :=
  TwinTDPatternOn p f fun m => 4 ≤ m ∧ m ≤ 7

theorem twinTDPatternOn_of_seven (hMFZ : FundNoncentral p) (hS : TwinTDSmallPattern7 p f) :
    TwinTDPatternOn p f fun m => 4 ≤ m := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  by_cases h8 : 8 ≤ m
  · obtain ⟨u, rfl⟩ : ∃ u, m = u + 3 + 5 := ⟨m - 8, by omega⟩
    obtain ⟨c⟩ := TCtx.nonempty_minus (by omega) S.odd S.five S.inClass S.exact
      (mem_conjClass_self K) S.cls S.p1 hshape
    exact PartnerPatternMinus.of_fixed_member_ge3 hMFZ c (single_class K) hshape hβ ht hKβ hfix
  · exact hS G hnab K z S m ⟨hm, by omega⟩ hshape β hβ t ht hKβ hfix

theorem twinTDSmallPattern_of_seven (hMFZ : FundNoncentral p) (hS : TwinTDSmallPattern7 p f) :
    TwinTDSmallPattern p f := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  exact twinTDPatternOn_of_seven hMFZ hS G hnab K z S m hm.1 hshape β hβ t ht hKβ hfix

end CFSG.ClassicalInvolution.RouteD.Gaps
