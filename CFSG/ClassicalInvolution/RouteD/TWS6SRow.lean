module

public import CFSG.ClassicalInvolution.RouteD.TWS6SRank
public import CFSG.ClassicalInvolution.RouteD.TWS6Cfg
public import CFSG.ClassicalInvolution.RouteD.TWEClose
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSmall

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS6

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

section Row

variable {p f : ℕ} [Fact p.Prime]

theorem twinYP1On_odd3_of_visible (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hVis : TwinYVisibleOn p f fun t n => t = .POmegaOdd ∧ n = 3) :
    TwinYP1On p f fun t n => t = .POmegaOdd ∧ n = 3 :=
  TWE.twinYP1On_of_visible_rowT hΩall
    (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4 hH
    (twinYGenTOn_of_model fun tY nY _ hl => by
      obtain ⟨rfl, rfl⟩ := hl
      exact twinMFGeneration_odd hp2 hq (le_refl 3))
    hVis

theorem twinYTypeOn_odd3_of_noCentral (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hVis : TwinYVisibleOn p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hNC : TwinYNoCentralOn p f fun t n => t = .POmegaOdd ∧ n = 3) :
    TwinYTypeOn p f fun t n => t = .POmegaOdd ∧ n = 3 :=
  TWE.twinYTypeOn_of_inputs_rowT hΩall
    (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4
    (TWE.twinYTransitiveOn_of_p1_rowT hΩall
      (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls))
      (twinYP1On_odd3_of_visible hp2 hq hΩall hP4 hH hcls hVis) hNC)
    (twinYRankOn_odd3 hp2 hq (twinYP1On_odd3_of_visible hp2 hq hΩall hP4 hH hcls hVis))

theorem twinYP1On_minus4_of_visible (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hVis : TwinYVisibleOn p f fun t n => t = .POmegaMinus ∧ n = 4) :
    TwinYP1On p f fun t n => t = .POmegaMinus ∧ n = 4 :=
  TWE.twinYP1On_of_visible_rowT hΩall
    (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4 hH
    (twinYGenTOn_of_model fun tY nY _ hl => by
      obtain ⟨rfl, rfl⟩ := hl
      exact twinMFGeneration_minus hp2 hq (le_refl 4))
    hVis

theorem twinYTypeOn_minus4_of_noCentral (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hcls : TwinInvolution p f)
    (hVis : TwinYVisibleOn p f fun t n => t = .POmegaMinus ∧ n = 4)
    (hNC : TwinYNoCentralOn p f fun t n => t = .POmegaMinus ∧ n = 4) :
    TwinYTypeOn p f fun t n => t = .POmegaMinus ∧ n = 4 :=
  TWE.twinYTypeOn_of_inputs_rowT hΩall
    (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4
    (TWE.twinYTransitiveOn_of_p1_rowT hΩall
      (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls))
      (twinYP1On_minus4_of_visible hp2 hq hΩall hP4 hH hcls hVis) hNC)
    (twinYRankOn_minus4 hp2 hq (twinYP1On_minus4_of_visible hp2 hq hΩall hP4 hH hcls hVis))

end Row

end CFSG.ClassicalInvolution.RouteD.TWS6
