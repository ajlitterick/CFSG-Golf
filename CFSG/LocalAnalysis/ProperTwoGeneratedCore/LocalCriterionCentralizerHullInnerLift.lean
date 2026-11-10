module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullAutomorphisms
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingConsequences

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.FiveTransitive.CharacteristicAutomorphism
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ShultStronglyClosedTI

universe u

variable {G : Type u} [Group G]


theorem characteristic_quotient_conj (N : Subgroup G) [N.Characteristic] (x : G) :
    quotient N (MulAut.conj x) = MulAut.conj (QuotientGroup.mk' N x) := by
  apply MulEquiv.ext
  intro y
  refine Quotient.inductionOn y ?_
  intro a
  change quotient N (MulAut.conj x) (QuotientGroup.mk' N a) =
    MulAut.conj (QuotientGroup.mk' N x) (QuotientGroup.mk' N a)
  simp only [quotient_apply_mk, MulAut.conj_apply, map_mul, map_inv]


end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
