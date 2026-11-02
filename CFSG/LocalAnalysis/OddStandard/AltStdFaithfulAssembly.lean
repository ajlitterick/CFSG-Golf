module

public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulSolomon
public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulAlt
public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulSL4
public import CFSG.Sporadic.Recognition.McLCentralizerCert
public import CFSG.Sporadic.Schreier.LyOuter
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.OddStandard.ResidualAlt
import CFSG.ClassicalInvolution.OrderForm
import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.OddStandard.ChildHe
public import CFSG.LocalAnalysis.OddStandard.ChildL34
public import CFSG.LocalAnalysis.OddStandard.ChildSmallAltOdd
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.YGroups.Y322Central
import CFSG.LinearAlgebra.LinearGroups.LinearTwo
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def AltStdCyclicW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) →
          Nonempty (G ≃* alternatingGroup (Fin (n + 4))) ∨ OddLieType G

end CFSG.OddStandard
