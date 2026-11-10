module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthLabelO
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthLabelU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFamRoute
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrth
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
import CFSG.Monster.GMS.Fi23Gen
import CFSG.Monster.GMS.Fi23GenIso
import CFSG.Monster.GMS.Fi23GenSix
import CFSG.Monster.GMS.LeechCoh
import CFSG.Monster.GMS.S365Center
import CFSG.Monster.GMS.S37
import CFSG.Monster.GMS.S4Assembly
import CFSG.Monster.GMS.S4CohB
import CFSG.Monster.GMS.S5Inputs
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.H13.J4OrderBase
import CFSG.Sporadic.Co1.Module.Co2Stab
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import CFSG.Sporadic.Schreier.J1QT
import CFSG.Sporadic.Schreier.M24
import CFSG.Sporadic.SuzOddCore.GraphData
import CFSG.Sporadic.SuzOddCore.SmallActionData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.StandardType (GGLabelRigidInput)

set_option linter.unusedSectionVars false


theorem i167COrth_holds : I167COrth := by
  intro S _ _ p Bb α J labK hp hp2 hFam hZ hBb hα hαp hInn hCover hCent hhalf hJc hJt
  have hD : COrthLabelDict :=
    { lnA := fun hq _ hn h => i167COrth_label_isLnA hq hn h
      omM := fun hq _ _ hn hk h => i167COrth_label_isOmMA hq hn hk h
      omP := fun hq _ _ hn hk hk3 h => i167COrth_label_isOmPA hq hn hk hk3 h
      unA := fun hq _ _ hm hf h => i167COrth_label_isUnA hq hm hf h }
  have hRig : GGLabelRigidInput := CFSG.StandardType.ggLabelRigidInput_holds
  have hb : CatDistinct.OrderBridge :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  obtain ⟨hN, ha1, hcat⟩ := i167COrth_catalog_of_innDiag hZ hFam hInn
  have hScp : ScpS p S Bb := hCover (by
    rcases hcat with h | h
    · exact pFreeCover_of_isOmPA hp hp2 hN ha1 h
    · exact pFreeCover_of_isOmMA hp hp2 hN ha1 h)
  have key : COrthConcl p S J := by
    by_cases h43 : labK.rank = 4 ∧ p = 3
    · exact i167COrth_route_d4 hD hRig hb hp hp2 hFam hZ hαp hInn hhalf hJc hJt h43.1
    · by_cases hBinn : ∀ β ∈ Bb, ∃ s : S, (MulAut.conj s : MulAut S) = β
      · exact i167COrth_inner hD hRig hb hp hp2 hFam hZ hBb hα hαp hInn hBinn hScp hCent hhalf hJc hJt
      · push Not at hBinn
        obtain ⟨β, hβ, hout⟩ := hBinn
        have hlab : Y10F.HasLabel S (fun l : GLALabel => l = labK) :=
          CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hInn
        rcases Y10GClsOrth.clsOrth_holds S p β labK hFam hp hp2 hZ hlab (hBb.2 β hβ) with
          hIb | hF | ⟨-, h4, h3⟩
        · exfalso
          obtain ⟨-, b, hb'⟩ := Y10GInnOrthMark.innDiagKind_orth_data hZ hFam hIb
          exact hout b hb'
        · exact i167COrth_route_field hD hRig hb hp hp2 hFam hZ hBb hα hαp hInn hScp hCent hhalf
            hJc hJt hβ hout hF h43
        · exact absurd ⟨h4, h3⟩ h43
  rcases key with ⟨hp3, n, hn, hc, h2⟩ | ⟨n, k, hn, hk, hpk, hc, h2⟩
  · exact Or.inr (Or.inl ⟨hp3, n, hn, hc, Or.inl h2⟩)
  · exact Or.inr (Or.inr ⟨n, k, hn, hk, hpk, hc, Or.inl h2⟩)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
