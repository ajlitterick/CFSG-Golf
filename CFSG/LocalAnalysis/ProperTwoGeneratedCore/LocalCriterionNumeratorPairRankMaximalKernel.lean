module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullConjugacy
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.TwoRankLowerBound.Helpers
open CFSG.BenderSuzuki.PFAppendixIII

universe u v

variable {G : Type u} [Group G]

@[expose] def numeratorPairRankPointClass (H : Subgroup G) (z w : G) : Set G :=
  involutionPointClass z ∩ (H : Set G) ∩
    (Subgroup.centralizer ({w} : Set G) : Set G)

theorem numeratorPairRankPointClass_normalized (H : Subgroup G) (z w : G) :
    H ⊓ Subgroup.centralizer ({w} : Set G) ≤
      Subgroup.normalizer (numeratorPairRankPointClass H z w) := by
  apply Subgroup.le_set_normalizer_iff.mpr
  intro a ha x hx
  refine ⟨⟨?_, H.mul_mem (H.mul_mem ha.1 hx.1.2) (H.inv_mem ha.1)⟩, ?_⟩
  · simpa only [rightConjugateElem, inv_inv] using
      pointClass_right_conjugate_mem hx.1.1 a⁻¹
  · exact (Subgroup.mem_normalizer_iff.mp
      (commute_normalizes_centralizer a w
        (Subgroup.mem_centralizer_singleton_iff.mp ha.2)) x).mp hx.2

theorem numeratorPairRank_opposite_normalized (I U : Subgroup G) (t : G)
    (hIU : I ≤ Subgroup.normalizer (U : Set G))
    (htI : t ∈ Subgroup.normalizer (I : Set G)) :
    I ≤ Subgroup.normalizer (U.map (MulAut.conj t).toMonoidHom : Set G) := by
  intro a ha
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hta : t⁻¹ * a * t ∈ I := (Subgroup.mem_normalizer_iff''.mp htI a).mp ha
  have hU : U.map (MulAut.conj (t⁻¹ * a * t)).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hIU hta)
  rw [Subgroup.map_map]
  change U.map ((MulAut.conj a).toMonoidHom.comp (MulAut.conj t).toMonoidHom) =
    U.map (MulAut.conj t).toMonoidHom
  have hmaps : (MulAut.conj a).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp (MulAut.conj (t⁻¹ * a * t)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hmaps, ← Subgroup.map_map, hU]


end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
