module

public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulSolomon
public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulAlt
public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulSL4
public import CFSG.Sporadic.Recognition.McLCentralizerCert
public import CFSG.Sporadic.Schreier.LyOuter
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Sporadic.Ly
public import CFSG.Sporadic.McL
public import CFSG.Timmesfeld.Orders.Classical
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
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.OddStandard.ChildHe
public import CFSG.LocalAnalysis.OddStandard.GlueL34
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
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
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.YGroups.Y322Central
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard

theorem not_dvd_card_Ly : ¬ 44352000 ∣ 51765179004000000 := by norm_num

theorem not_dvd_card_McL : ¬ 44352000 ∣ 898128000 := by norm_num

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
