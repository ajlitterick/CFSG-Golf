module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogResidual
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddBasic
public import CFSG.RankThree.PartOne.CTP.StrongPAssembly
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddLie
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureAlt
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureSporOrder
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureSporChar
import CFSG.RankThree.PartOne.CTP.StrongPThree
import CFSG.RankThree.PartOne.CTP.SpinRankFour
import CFSG.RankThree.PartOne.CTP.BabyRankFour
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.Adapters.CatalogAgree
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableCompactPresented
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.Kernel.HNLocalSound
public import CFSG.Foundations
public import CFSG.LieType.BorelTits.OrthogonalEven
public import CFSG.LieType.BorelTits.Unitary
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Ree.TitsWeyl
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Fi22
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Perm.ChainComplete
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1Bridge
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Sporadic.Bridge.Fi24Data
public import CFSG.Sporadic.Bridge.J4SurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Bridge.McLSurj
public import CFSG.Sporadic.Co3
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.He
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.ON.ActionBase
public import CFSG.Sporadic.ON.CertificateBase
public import CFSG.Sporadic.ON.ChainBase
public import CFSG.Sporadic.ON.LinesBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Co1
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.Co3
public import CFSG.Sporadic.Presentation.Fi24PrimeExact
public import CFSG.Sporadic.Presentation.HeExact
public import CFSG.Sporadic.Presentation.J4
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Presentation.M23
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Presentation.ONan
public import CFSG.Sporadic.Presentation.ThBase
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Th
public import CFSG.Sporadic.Th.CertificateBase
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.RankThree.PartTwo.Census.Spin.Main
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.Sporadic.Bridge.Catalogue
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Assembly CFSG.Blueprint CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.Census3 TauCeti
open CFSG.Open (rankThreeUC)

@[expose] def CatalogNoUCSporadic (G : Type) [Group G] [Finite G] : Prop :=
  Standing G → (Nonempty (G ≃* NativeSporadic.Carrier .Co2) ∨
    Nonempty (G ≃* NativeSporadic.Carrier .Th)) → ¬ rankThreeUC G

@[expose] def CharTwoCases (G : Type) [Group G] : Prop :=
  PSLTwoCase G ∨ PSpTwoCase G ∨ POmegaTwoCase G ∨ PSUTwoCase G ∨ ExceptionalTwoCase G

section CharTwo

variable {G : Type} [Group G]

theorem twoCase_of_isoLie (hB : SeitzBridge) {d : LieTypeIndex} (hd : d.characteristic = 2)
    (h : IsoLie G d) : CharTwoCases G := by
  obtain ⟨t, n, r, f, hadm, hmodel, hr, -, -⟩ := hB G d h
  obtain rfl : r = 2 := hr.trans hd
  rcases hmodel with ⟨ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, -, hm⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨n, f, hm⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, f, hm⟩)))
    · exact Or.inr (Or.inl ⟨n, f, hm⟩)
    · exact absurd rfl hadm.2.2.2
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨n, f, hm⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨n, f, hm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, f, ht, hm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, f, ht, hm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, hm⟩)))))

theorem twoCase_of_item7 (hB : SeitzBridge) (h : ThmThreeItem7 G) : CharTwoCases G := by
  rcases h with ⟨q, hq, h⟩ | ⟨m, h⟩ | ⟨q, hq, h⟩ | ⟨m, h⟩ | h
  · exact twoCase_of_isoLie hB (by simp [hq]) h
  · exact twoCase_of_isoLie hB (by simp) h
  · rcases h with h | h | h | h | h | h | h <;> exact twoCase_of_isoLie hB (by simp [hq]) h
  · exact twoCase_of_isoLie hB (by simp) h
  · exact twoCase_of_isoLie hB (by simp) h

theorem twoCase_of_item8 (hB : SeitzBridge) (h : ThmThreeItem8 G) : CharTwoCases G := by
  obtain ⟨q, hq, h⟩ := h
  rcases h with h | h | h <;> exact twoCase_of_isoLie hB (by simp [hq]) h

theorem twoCase_of_item9 (hB : SeitzBridge) (h : ThmThreeItem9 G) : CharTwoCases G := by
  obtain ⟨q, hq, -, h⟩ := h
  rcases h with h | h | h | h | h | h | h <;> exact twoCase_of_isoLie hB (by simp [hq]) h

end CharTwo

section Certified

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem Standing.sporadic_of_item6 (hS : Standing G) (h : ThmThreeItem6 G) :
    Nonempty (G ≃* NativeSporadic.Carrier .Co2) ∨ Nonempty (G ≃* NativeSporadic.Carrier .Th) := by
  obtain ⟨s, hs, ⟨e⟩⟩ := h
  obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
  have e' : G ≃* NativeSporadic.Carrier s := e.trans b.symm
  simp only [sporadicsThm3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hS.false_of_M11 e').elim
  · exact (hS.false_of_M12 e').elim
  · exact (hS.false_of_M22 e').elim
  · exact (hS.false_of_M23 e').elim
  · exact (hS.false_of_M24 e').elim
  · exact (hS.false_of_J1 e').elim
  · exact (hS.false_of_J2 e').elim
  · exact (hS.false_of_J3 e').elim
  · exact (hS.false_of_J4 e').elim
  · exact (hS.false_of_McL e').elim
  · exact (hS.false_of_Ly e').elim
  · exact (hS.false_of_HS e').elim
  · exact (hS.false_of_He e').elim
  · exact (hS.false_of_Suz e').elim
  · exact (hS.false_of_Ru e').elim
  · exact (hS.false_of_ON e').elim
  · exact (hS.false_of_Co3 e').elim
  · exact Or.inl ⟨e'⟩
  · exact (hS.false_of_HN e').elim
  · exact Or.inr ⟨e'⟩

theorem catalogNoUCResidual_of_sporadic (h : CatalogNoUCSporadic G) : CatalogNoUCResidual G := by
  intro hS hC hpsl hpsp hpom hpsu hexc _ hUC
  have hIn : InCatalog G := CFSG.Open.QTFaithfulEmptyTauCeti.inCatalog_of_catalog G hC
  have hList : TheoremThreeList G := threeCatalog_of_spin spinRankFour rankFourBabyMonster G (hS.theoremThreeHyp hIn)
  have hchar : ¬ CharTwoCases G := by
    rintro (h | h | h | h | h)
    exacts [hpsl h, hpsp h, hpom h, hpsu h, hexc h]
  rcases hList with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact hS.false_of_item1 h1
  · exact hS.false_of_item2 h2
  · exact hS.false_of_item3 h3
  · exact hS.false_of_item4 h4
  · exact hS.false_of_item5 h5
  · exact h hS (hS.sporadic_of_item6 h6) hUC
  · exact hchar (twoCase_of_item7 seitzBridge h7)
  · exact hchar (twoCase_of_item8 seitzBridge h8)
  · exact hchar (twoCase_of_item9 seitzBridge h9)

end Certified

end CFSG.LocalAnalysis.RankThreeUC
