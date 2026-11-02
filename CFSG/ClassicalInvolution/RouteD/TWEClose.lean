module

public import CFSG.ClassicalInvolution.RouteD.TWEFinal
public import CFSG.ClassicalInvolution.RouteD.TWEBigAET

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

section Close

variable {p f : ℕ} [Fact p.Prime]

theorem aEmptyTwinRowOn_large (hΩall : HypOmegaModAll p f) (hcls : TwinInvolution p f) :
    AEmptyTwinRowOn p f TwinRow.large :=
  AEmptyTwinRow.on (Big.aEmptyTwinRow_proved hΩall hcls)

theorem twinDExistsSmall₄₆_of_four_Y4 (h4 : TwinDExistsCase p f 4) (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hY4 : TwinYPatternAt p f .POmegaPlus 6 (@PartnerPatternD p f 6 _)) :
    TwinDExistsSmall₄₆ p f :=
  twinDExistsSmall₄₆_of_four h4 hΩall (aEmptyTwinRowOn_large hΩall hcls) hP4 hH hcls hY4

theorem twinYP1On_large_proved (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f) :
    TwinYP1On p f TwinRow.large :=
  twinYP1On_large_of_aEmptyTwinRow hp2 hq hΩall (aEmptyTwinRowOn_large hΩall hcls) hP4 hH

theorem twinYTypeOn_large_proved (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f) :
    TwinYTypeOn p f TwinRow.large :=
  twinYTypeOn_large_of_aEmptyTwinRow hp2 hq hΩall (aEmptyTwinRowOn_large hΩall hcls) hP4 hH

end Close

end CFSG.ClassicalInvolution.RouteD.TWE
