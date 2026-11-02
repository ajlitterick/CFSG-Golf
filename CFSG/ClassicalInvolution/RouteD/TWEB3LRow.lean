module

public import CFSG.ClassicalInvolution.RouteD.TWEB3LPartner
public import CFSG.ClassicalInvolution.RouteD.TWS6SRow

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

section Row

variable {p f : ℕ} [Fact p.Prime]


theorem twinBExistsCase_three_of_Y124L (hcls : TwinInvolution p f)
    (hY1 : TwinYP1On p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hY2 : TwinYTypeOn p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hY4 : TwinYPatternAtL p f .POmegaOdd 3 (@PartnerPatternBPair p f 3 _)) :
    TwinBExistsCase p f 3 :=
  twinBExistsCase_of_YL (m := 3) (by norm_num) ⟨rfl, rfl⟩ hY1 hY2
    (twinYPartnerLOn_mono (fun t n h => ⟨h.1, by omega⟩) (twinYPartnerLOn_odd hcls)) hY4

theorem twinBExistsCase_three_of_visible_noCentral_YL (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hVis : TwinYVisibleOn p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hNC : TwinYNoCentralOn p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hY4 : TwinYPatternAtL p f .POmegaOdd 3 (@PartnerPatternBPair p f 3 _)) :
    TwinBExistsCase p f 3 := by
  intro G _ _ _ hnab K z S m hm hshape
  exact twinBExistsCase_three_of_Y124L hcls
    (TWS6.twinYP1On_odd3_of_visible S.odd S.five hΩall hP4 hH hcls hVis)
    (TWS6.twinYTypeOn_odd3_of_noCentral S.odd S.five hΩall hP4 hH hcls hVis hNC) hY4 G hnab K z S m
    hm hshape

end Row

end CFSG.ClassicalInvolution.RouteD.TWE.B3
