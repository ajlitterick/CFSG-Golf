module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FExcL33
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FExcCN
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FORow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FURow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FExc
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCOmInv
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1All
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2E6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE2E
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE2F4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE2G2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE2D4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE2TwE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRAll
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Ree
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Alt
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSU
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddTriality
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreBalB
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphAlt
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedNonsquare
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Sporadic.Co1.Module.Involutions
public import CFSG.Sporadic.Co1.Module.TwoBCertBase
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.HeldB.OuterFixed
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup Assembly.LowTwoRank

theorem twoNilpFor'_chevalleyExceptional
    (hCO : E1.ChevOddInnerInput) :
    TwoNilpFor' fun Y _ => ∃ (t : StatedLieTag) (p f : ℕ),
      t ∈ Blueprint.chevalleyExceptionalTags ∧ Blueprint.ChevalleyExceptionalModel Y t p f := by
  refine ((E1.twoNilpFor_chevOdd hCO).weaken.or (E2.twoNilpFor_of_E6 E2.involutionCentralizerNotTwoGroup_G2 E2.involutionCentralizerNotTwoGroup_F4 E2.involutionCentralizerNotTwoGroup_E7 E2.involutionCentralizerNotTwoGroup_E8 E2.involutionCentralizerNotTwoGroup_trialityD4 (E2.twoNilpFor_E6 E2.involutionCentralizerNotTwoGroup_E6 E2.involutionCentralizerNotTwoGroup_twistedE6 E2.involutionCentralizerNotTwoGroup_F4)).weaken).mono
    fun Y _ hY => ?_
  obtain ⟨t, p, f, ht, hm⟩ := hY
  by_cases hp : p = 2
  · subst hp
    exact Or.inr ⟨t, f, ht, hm⟩
  · exact Or.inl ⟨t, p, f, hp, ht, hm⟩

end CFSG.ComponentClassification.HarrisLit.L33


namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup Assembly.LowTwoRank

theorem harris81Lemma33Simple_of_open (hGA : TBLit.GriessMultipliersAllModels)
    (hCO : E1.ChevOddInnerInput) : Harris81Lemma33Simple :=
  harris81Lemma33Simple_of_twoNilp' hGA OC.twoNilpFor_odd.weaken
    (C2.twoNilpFor'_classical_two twoNilpFor_alt C2.twoNilpFor_psu C2.twoNilpFor_pOmegaPlus
        C2.twoNilpFor_pOmegaMinus) (twoNilpFor'_chevalleyExceptional hCO)
    Ree.twoNilpFor_reeTits.weaken
    fun s => (twoNilpFor_isSporadic_holds s).weaken

end CFSG.ComponentClassification.HarrisLit.L33

namespace CFSG.ComponentClassification.GSThmB

open CFSG HarrisLit.L33

theorem cfTwoNilpSL2_of_open (hGA : TBLit.GriessMultipliersAllModels)
    (hCO : E1.ChevOddInnerInput) : CFTwoNilpSL2 :=
  cfTwoNilpSL2_of_rows' hGA twoNilpFor_alt.weaken
    (twoNilpFor_classicalRep' OC.twoNilpFor_odd.weaken (C2.twoNilpFor'_classical_two twoNilpFor_alt
        C2.twoNilpFor_psu C2.twoNilpFor_pOmegaPlus C2.twoNilpFor_pOmegaMinus))
    (twoNilpFor_exceptionalRep' (twoNilpFor'_chevalleyExceptional hCO)
      Ree.twoNilpFor_reeTits.weaken)
    (twoNilpFor_sporadicRep' fun s => (twoNilpFor_isSporadic_holds s).weaken)

end CFSG.ComponentClassification.GSThmB
