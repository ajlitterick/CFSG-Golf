module

public import CFSG.ClassicalInvolution.RouteD.TWEB4Case
public import CFSG.ClassicalInvolution.RouteD.TWEB4Fixed
public import CFSG.ClassicalInvolution.RouteD.TWEB6Main

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B4

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem twinBExistsCase_four (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f) : TwinBExistsCase p f 4 := by
  intro G _ _ _ hnab K z S m hm hshape
  subst hm
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨Fact.out, hf, by norm_num, S.odd⟩
  obtain ⟨c⟩ := TCtx.nonempty_odd (by norm_num : 3 ≤ 4) S.odd S.five S.inClass S.exact
    (mem_conjClass_self K) S.cls S.p1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_odd (by norm_num) hadm (single_class K)
    hshape
  exact ⟨β, hβ, t, ht, hKβ, twinBCase_four hΩall hP4 hH hcls G hnab K z S hshape β hβ t ht hKβ hfix⟩

theorem twinBExistsSmallRest_of_three_proved (h3 : TwinBExistsCase p f 3)
    (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hcls : TwinInvolution p f) : TwinBExistsSmallRest p f :=
  TWE.B6.twinBExistsSmallRest_of_three_four hΩall hP4 hH hcls h3
    (twinBExistsCase_four hΩall hP4 hH hcls)

end Main

end CFSG.ClassicalInvolution.RouteD.TWE.B4
