module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNLeaves
public import CFSG.GH74.GLS.C3.Layer1.St1EndNSoc
public import CFSG.CGT.Foote81L6.TStruct.DihSub
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.NormalQuaternion
public import CFSG.GH74.AS16.Defs
public import CFSG.GH74.E2.Components
public import CFSG.GH74.E2.OddRankG
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.EvenAltConfig
public import CFSG.GH74.GLS.C3.Layer1.EvenStd
public import CFSG.GH74.GLS.C3.Layer1.Th2P73
public import CFSG.GH74.GLS.C3.Layer1.Th2P812
public import CFSG.GH74.GLS.C3.Layer1.Th2Sig10
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.Lifted.Rnormal4
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.Equivariance
public import CFSG.Goldschmidt75.Sig32Core
public import CFSG.Goldschmidt75.Sig3Four
public import CFSG.Goldschmidt75.Sig3Trans
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.OddOrderClosurePResidual
public import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Map
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Step
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingReduction
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Th.Max3.Core
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

@[expose] def B_st1_prop71_lemma711_simple : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Gen4 X → IsKGroupNative X →
    ∀ L : Subgroup X, IsSimpleSocle L ⊤ → GHList ↥L →
      ∀ (K : Subgroup X) (x y : X), K ≤ L → orderOf x = 2 → orderOf y = 2 → x * y = y * x →
        IsCompIn (centralizer ({x} : Set X)) K →
        HasL2Model (↥K ⧸ pPrimeCore 2 ↥K) (fun q => q = 9) →
        Th2.P85.IsTerminalSub K →
        (∀ u : X, orderOf u = 2 → (∀ k ∈ K, u * k = k * u) → u * x = x * u → u = x) →
        ¬ (pPrimeCoreOf 2 (centralizer ({y} : Set X)) ⊓ centralizer ({x} : Set X) ≤
            centralizerSection K (pPrimeCoreOf 2 K)) →
        4 ≤ pRank 2 ↥(centralizer ({x} : Set X)) →
        (pRank 2 ↥(centralizer ({x} : Set X)) = pRank 2 X →
          x ∈ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆) →
        False

theorem b_st1_prop71_lemma711_of_simple (hS : B_st1_prop71_lemma711_simple) :
    B_st1_prop71_lemma711 := by
  intro X _ _ hgen hKG hcore hGH K x y hx2 hy2 hxy hKc hL9 hterm hh h2 h3 h4
  by_contra hKns
  have hKq : CFSG.IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKc.1) hKc.2.1
  rcases C3.Layer1.EndN.Soc.socle_or_swap hcore hx2 hKq hKc hterm hKns with
    ⟨Λ, hΛ, hKΛ⟩ | ⟨Λ, hΛ, hne, hcomps⟩
  · exact hS X hgen hKG Λ hΛ (hGH Λ hΛ) K x y hKΛ hx2 hy2 hxy hKc hL9 hterm hh h2 h3 h4
  · have hle : pRank 2 ↥(centralizer ({x} : Set X)) ≤ pRank 2 X :=
      Bg.pRank_subgroup_le one_lt_two _
    have hX4 : pRank 2 X ≤ 4 := hgen.pRank_two_le
    exact C3.Layer1.EndN.Soc.not_mem_commutator_of_swap hΛ hne hcomps (h4 (by omega))

end CFSG.GH74.GLS
