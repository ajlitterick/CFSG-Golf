module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PairGenerationDischarge

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.ProperTwoGeneratedCore.CosetNormalizer CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
open CFSG.BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative Pointwise

theorem linearSuzukiPointKernelRootProduct_holds
    (G : Type) [Group G] [Finite G] :
    LinearSuzukiPointKernelRootProduct G := by
  intro H z h beta hbeta t ht hrank w hwE hw hwz hwt i hi hfix
  obtain ⟨R₀⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨Rv⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z (w * z) ⊓ H)) := inferInstance
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  have key := fun (R : Sylow 2 ↥(localInvolutionPointHull z w ⊓ H))
      (T₁ : Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) =>
    RankOnePair.linear_Suzuki_pair_centralizer_point_kernel_is_root_product h
      (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G)
      (pairCommutatorGenerationTheorem G) beta hbeta ht hrank hwE hw hwz hwt hi hfix R Rv T₁
  obtain ⟨-, -, -, -, -, -, -, -, hK, -⟩ := key R₀ T₀
  refine ⟨fun R => ?_, hK, fun R T₁ => ?_⟩
  · obtain ⟨-, -, -, -, hcard, -⟩ := key R T₀
    exact hcard
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he, hBA⟩ := key R T₁
    exact ⟨he, hBA⟩

theorem solvableLinearCosetNormalizerTheorem_holds
    (G : Type) [Group G] [Finite G] :
    SolvableLinearCosetNormalizerTheorem G :=
  solvableLinearCosetNormalizerTheorem_of_parts (pairCommutatorGenerationTheorem G)
    (linearSuzukiPointKernelRootProduct_holds G) (linearSuzukiHullOddCoreTrivial_holds G)


theorem theoremTwo_of_unitaryMonomial
    (h : ∀ (G : Type) [Group G] [Finite G], UnitaryMonomialTheorem G) :
    Assembly.TheoremTwo :=
  theoremTwo_of_solvable_and_monomial fun G _ _ =>
    ⟨solvableLinearCosetNormalizerTheorem_holds G, h G⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair
