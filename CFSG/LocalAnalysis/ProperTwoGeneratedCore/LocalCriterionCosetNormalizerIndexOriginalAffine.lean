module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexUnitAffine
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorOddKernelFull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorUnifiedParameter

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

universe v

variable {G : Type v} [Group G]

theorem originalPointRoot_le_entire_hull (H : Subgroup G) (z u : G) :
    originalPointRoot H z u ≤ localInvolutionPointHull z u :=
  Subgroup.closure_mono fun _ hx => hx.1

theorem originalPointRoot_entire_commutes_u (H : Subgroup G) (z u : G) :
    ∀ x ∈ originalPointRoot H z u, Commute u x := by
  intro x hx
  exact (show Commute x u from Subgroup.mem_centralizer_singleton_iff.mp
    (localInvolutionPointHull_le_centralizer z u
      (originalPointRoot_le_entire_hull H z u hx))).symm

theorem original_entire_hull_centralizer_le_root_centralizer
    (H : Subgroup G) (z u : G) :
    Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.centralizer (localInvolutionPointHull z u : Set G) ≤
      Subgroup.centralizer (originalPointRoot H z u : Set G) :=
  inf_le_right.trans
    (Subgroup.centralizer_le (originalPointRoot_le_entire_hull H z u))

theorem original_entire_hull_centralizer_le_entire_coset_centralizer
    (H : Subgroup G) (z u : G) :
    Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.centralizer (localInvolutionPointHull z u : Set G) ≤
      Subgroup.centralizer
        ((fun x : G => u * x) '' (originalPointRoot H z u : Set G)) := by
  rw [unit_translate_entire_centralizer]
  exact le_inf inf_le_left (original_entire_hull_centralizer_le_root_centralizer H z u)

theorem original_entire_hull_centralizer_le_affine_kernel
    (H : Subgroup G) (z u : G) (hu : u * u = 1) :
    let U := originalPointRoot H z u
    let N := Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))
    let K := Subgroup.centralizer ({u} : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z u : Set G)
    K.subgroupOf N ≤
      (unitAffineHom U u hu (originalPointRoot_entire_commutes_u H z u)).ker := by
  dsimp only
  rw [unitAffineHom_ker]
  intro n hn
  exact ⟨hn.1, original_entire_hull_centralizer_le_root_centralizer H z u hn⟩


end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
