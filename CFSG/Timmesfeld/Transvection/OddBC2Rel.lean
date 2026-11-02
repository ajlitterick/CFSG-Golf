module

public import CFSG.Timmesfeld.Transvection.OddBC2RelStatement
public import CFSG.Timmesfeld.Transvection.OddUnitary
import CFSG.Timmesfeld.Transvection.OddHeisTwist
import CFSG.Timmesfeld.Transvection.OddHeisRelations
import CFSG.Timmesfeld.Transvection.OddBC2Main
public import CFSG.Fischer.Assembly
public import CFSG.Fischer.Classification.Milestone
public import CFSG.Fischer.NoF25.Local
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Timmesfeld.Transvection.OddBC2Statement

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.LieType.BorelTits


theorem oddFrameHeisRelations : OddFrameHeisRelations := by
  intro H _ Δ h hML hq F _ _ _ n hFn _ hcard r hr hm P Q hF hns R hR _ _ θ hθr _ hθo hθc hθmem
    hd
  obtain ⟨e, hSM⟩ := IsMaxFrame.exists_tw_commutatorElement_ξ_map_suHeis hFn hr hm h hML hq hF
    hns hcard hR hθr hθo hθc hθmem hd
  obtain ⟨h1, h2⟩ := IsMaxFrame.commutatorElement_suHeis_of_tw hFn hr hm h hML hq hF hns hcard
    hR hθr hθo hθc hθmem hd e hSM
  cases e
  · simp only [RelBuild.tw_false] at h1 h2
    exact Or.inl ⟨h1, h2⟩
  · refine Or.inr ⟨fun u v u' v' hv hv' => ?_, fun s u v hv => ?_⟩
    · rw [h1 u v u' v' hv hv', RelBuild.tw_true, map_mul, unitaryInvolution_involutive hFn]
    · rw [h2 s u v hv, RelBuild.tw_true, RelBuild.tw_true, unitaryInvolution_involutive hFn]

theorem oddUnitaryStatement_holds : OddUnitaryStatement :=
  oddUnitaryStatement_of_heisRelations oddFrameHeisRelations

end CFSG.Timmesfeld.Transvection
