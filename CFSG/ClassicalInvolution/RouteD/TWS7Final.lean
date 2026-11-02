module

public import CFSG.ClassicalInvolution.RouteD.TWS7Model
public import CFSG.ClassicalInvolution.RouteD.TWS7Asm
public import CFSG.ClassicalInvolution.RouteD.TwinSmallCasesD
public import CFSG.ClassicalInvolution.RouteD.TwinYExistsD
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS7

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps

set_option linter.unusedSectionVars false

section Final

variable {p f : ℕ} [Fact p.Prime]

theorem twinDExistsCase_four : TwinDExistsCase p f 4 := by
  intro G _ _ _ hnab K z S m hm hshape
  obtain rfl : m = 4 := hm
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf, le_refl 4⟩
  obtain ⟨c⟩ := TCtx.nonempty_plus (le_refl 4) S.odd S.five S.inClass S.exact
    (mem_conjClass_self K) S.cls S.p1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_plus (le_refl 4) hadm (single_class K)
    hshape
  exact ⟨β, hβ, t, ht, hKβ, partnerPatternD_four_of_model modelLeafD_proved (fundNoncentral p) c
    (single_class K) hshape hβ ht hKβ hfix⟩

end Final

end CFSG.ClassicalInvolution.RouteD.TWS7
