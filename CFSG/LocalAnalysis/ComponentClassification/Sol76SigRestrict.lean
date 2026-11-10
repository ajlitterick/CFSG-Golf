module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigForced
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LargeExtraspecial.Types
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39G
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.Sol76False316
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Props
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Functor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Schreier.RuLOdd
public import CFSG.Sporadic.Schreier.RuZClass
public import CFSG.Sporadic.ThSchreier.GlobalIndexBase
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

@[expose] def IsSolomonI (X : Type) [Group X] : Prop :=
  Nonempty ((X ⧸ center X) ≃* ↥CFSG.Open.properTwoGenCoreJ1) ∨
    CFSG.Open.StatedClassicalModel (X ⧸ center X) .PSL 3 2 2 ∨
    CFSG.Open.fusionIsBenderGroup (X ⧸ center X) ∨
    (Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 9)) ∧ Nat.card (center X) = 2)

variable {G : Type} [Group G] [Finite G]

abbrev coreQuot (K : Subgroup G) : Type := ↥K ⧸ pPrimeCore 2 ↥K

@[expose] def SolRestricted (N K K' : Subgroup G) : Prop :=
  (kStarComponents N).ncard = 2 →
    ¬ (IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') ∧
        2 < CFSG.Open.pRank 2 K' ∧ ¬ IsSolomonI (coreQuot K')) ∧
      ¬ ((Nonempty ((coreQuot K ⧸ center (coreQuot K)) ≃* alternatingGroup (Fin 9)) ∧
          Nat.card (center (coreQuot K)) = 2) ∧
        CFSG.Open.StatedClassicalModel (coreQuot K') .PSL 2 7 1)

@[expose] def solRestricted : SigOrientation := fun _ _ _ N K K' => SolRestricted N K K'


end CFSG.ComponentClassification.Sol76.Sig
