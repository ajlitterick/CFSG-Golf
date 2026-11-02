module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28TorusNormalizer
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentIrred
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupJ4
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterHolds
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.ClassicalGroups
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAtProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACentralBaseXQ
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3LinTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralU
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Main
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.Sporadic.Bridge.J4SurjInputs
public import CFSG.Sporadic.Bridge.McLSurj
public import CFSG.Sporadic.Presentation.J4
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import CFSG.LieType.Chevalley.EvenRootCommutatorF4
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4RRepBase
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.Quasithin.Background.C2Inputs
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.Sporadic.J4.QT2LocCntMainBase
import CFSG.Walter.FinalRee
import CFSG.Walter.Ree.Thompson2.BaseFin
import CFSG.Walter.ReeOrder.WardLocal
import CFSG.Walter.W67.Section8.Prop83
import Certificates.Data.HSFiveCheck

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace NineFourIrred

theorem pRank_top_eq_two {Z : Type} [Group Z] [Finite Z] {p : ℕ} {Y : Subgroup Z}
    (h : Open.pRank p Y = 2) : Open.pRank p (⊤ : Subgroup ↥Y) = 2 :=
  (CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y).symm.trans h

theorem exponent_le_pRank_linTwo {K : Type} [Group K] [Finite K] {p : ℕ}
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.p = p) (hd : d.1 = .A 1 q)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : q.exponent ≤ Open.pRank p (⊤ : Subgroup K) := by
  subst hq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨b⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
    (p := q.p) (n := q.exponent) ⟨q, hd, rfl, rfl⟩
  have h := CFSG.Quasithin.H13.S3320.le_pRank_of_psl2 q.exponent_pos (e.trans b)
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h

theorem four_le_pRank_unitary {K : Type} [Group K] [Finite K] {p : ℕ} (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.p = p) (h2 : 2 ≤ q.exponent)
    (hd : d.1 = .twistedA 2 q) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    4 ≤ Open.pRank p (⊤ : Subgroup K) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .twistedA 2 q := hd
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  subst hq
  obtain ⟨-, -, h⟩ := CFSG.SectionRank.classical_model_rank hp2 hC
  rcases h with ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | ⟨h, -⟩ | h
  · exact absurd h (by decide)
  · omega
  · omega
  · exact absurd h (by decide)
  · omega

theorem three_le_pRank_ree
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} {m : ℕ}
    (hd : d.1 = .reeG2 m) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .reeG2 m := hd
  obtain ⟨-, h3, hr⟩ := CFSG.SectionRank.smallReeModel_rank
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨e⟩⟩)
  omega

end NineFourIrred

theorem kFactNineFourSylowIrred_holds :
    KFactNineFourSylowIrred := by
  intro p hp hp2 Z _ _ Y hY hrk S
  haveI : Fact p.Prime := ⟨hp⟩
  have hrk' := NineFourIrred.pRank_top_eq_two hrk
  obtain ⟨-, i, hi, ⟨e⟩⟩ := hY
  have step : RankOneCent.IsStepThreeIndex p i → NormIrredFrattini (S : Subgroup ↥Y) :=
    fun h => (RankOneCent.kFactStepThreeIrred_holds p ↥Y ⟨i, h, ⟨e⟩⟩ S).1
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating n _ => exact step hi
  | lie d =>
    rcases hi with ⟨q, hqp, h2, hd⟩ | ⟨q, hqp, hd⟩ | ⟨rfl, m, hm⟩ |
      ⟨rfl, ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq2', hd⟩⟩ | ⟨rfl, hd | hd⟩
    ·
      by_cases hn : q.exponent = 2
      · obtain ⟨e₂⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := p)
          (n := 2) (d := d) ⟨q, hd, hqp, hn⟩
        exact (RankOneCent.Irred.irredAt_psl_two hp2 (e.trans e₂) S).1
      · exfalso
        have := NineFourIrred.exponent_le_pRank_linTwo hqp hd e
        omega
    ·
      by_cases hn : q.exponent = 1
      · exact (RankOneCent.Irred.irredAt_unitary hp hp2 hqp hn hd e S).1
      · exfalso
        have := q.exponent_pos
        have := NineFourIrred.four_le_pRank_unitary hp2 hqp (by omega) hd e
        omega
    ·
      exfalso
      have := NineFourIrred.three_le_pRank_ree hm e
      omega
    ·
      exfalso
      have hL : CFSG.AGLEmbedding.IsCaseTwoGroup 3 ↥Y :=
        ⟨d, Or.inl ⟨rfl, q, hq2, hq3, hd⟩, ⟨e⟩⟩
      have := InnerQ.pRank_top_le_one_of_isCyclic S
        (CFSG.AGLEmbedding.l28_isCyclic_sylow_three hL S)
      omega
    ·
      exact step (Or.inl ⟨rfl, Or.inr (Or.inr ⟨q, hq2, hq2', hd⟩)⟩)
    ·
      exfalso
      obtain ⟨d1, hv⟩ := d
      obtain rfl : d1 = .suzuki 2 := hd
      obtain ⟨hc, -⟩ := Generic41Spor.sz32_sylow ↥Y ⟨rfl, hv, ⟨e⟩⟩ S
      have := InnerQ.pRank_top_le_one_of_isCyclic S hc
      omega
    ·
      exact step (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr hd))⟩)
  | sporadic s =>
    rcases hi with h | h | ⟨rfl, rfl⟩
    ·
      exact step (Or.inl h)
    ·
      exact step (Or.inr h)
    ·
      have hJ : Generic41Spor.IsJ4Type 11 ↥Y := ⟨rfl, ⟨e⟩⟩
      obtain ⟨hcard, hnc, -⟩ := Generic41Spor.j4_sylow ↥Y hJ S
      exact (RankOneCent.Irred.irredAt_of_heis hcard hnc
        (RankOneCent.Irred.hirr_of_between (Generic41Spor.j4_irreducible ↥Y hJ S))).1

end CFSG.LocalAnalysis.RankThreeTheoremC
