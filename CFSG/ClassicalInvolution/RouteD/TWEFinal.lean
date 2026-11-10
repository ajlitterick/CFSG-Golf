module

public import CFSG.ClassicalInvolution.RouteD.TWELarge

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

section Final

variable {p f : ℕ} [Fact p.Prime]

theorem twinDExistsCase_six_of_residuals (hΩall : HypOmegaModAll p f)
    (hAT : AEmptyTwinRowOn p f TwinRow.large) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hcls : TwinInvolution p f)
    (hY4 : TwinYPatternAt p f .POmegaPlus 6 (@PartnerPatternD p f 6 _)) :
    TwinDExistsCase p f 6 := by
  intro G _ _ _ hnab K z S m hm hshape
  exact twinDExistsCase_of_Y (m := 6) (by norm_num) (P := TwinRow.large)
    (Or.inl ⟨rfl, by norm_num⟩)
    (twinYP1On_large_of_aEmptyTwinRow S.odd S.five hΩall hAT hP4 hH)
    (twinYTypeOn_large_of_aEmptyTwinRow S.odd S.five hΩall hAT hP4 hH)
    (TWD.twinYPartnerOn_large hcls) hY4 G hnab K z S m hm hshape

theorem twinDExistsSmall₄₆_of_four (h4 : TwinDExistsCase p f 4) (hΩall : HypOmegaModAll p f)
    (hAT : AEmptyTwinRowOn p f TwinRow.large) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hcls : TwinInvolution p f)
    (hY4 : TwinYPatternAt p f .POmegaPlus 6 (@PartnerPatternD p f 6 _)) :
    TwinDExistsSmall₄₆ p f := by
  intro G _ _ _ hnab K z S m hm hshape
  rcases hm with rfl | rfl
  · exact h4 G hnab K z S 4 rfl hshape
  · exact twinDExistsCase_six_of_residuals hΩall hAT hP4 hH hcls hY4 G hnab K z S 6 rfl hshape

end Final

end CFSG.ClassicalInvolution.RouteD.TWE
