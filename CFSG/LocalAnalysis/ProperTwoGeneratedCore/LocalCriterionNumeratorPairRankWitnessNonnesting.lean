module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairRootNonnestingFull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionPairRootNonnesting
open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

theorem numeratorPairRank_pair_join_eq_closure (u v : G) :
    Subgroup.zpowers u ⊔ Subgroup.zpowers v = Subgroup.closure ({u, v} : Set G) := by
  have hpair : ({u, v} : Set G) = {u} ∪ {v} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  rw [hpair, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

theorem numeratorPairRankPointClass_eq_rootFixedSet
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (w : G) :
    numeratorPairRankPointClass H z w = rootFixedSet H z w := by
  rw [numeratorPairRankPointClass, rootFixedSet,
    original_point_class_intersection_eq_conjugacyWithin h]

variable [Finite G]

omit [Group G] in
theorem numeratorPairRank_class_eq_of_subset_of_card_le
    {A B : Set G} (hAB : A ⊆ B) (hcard : Nat.card B ≤ Nat.card A) : A = B := by
  apply Set.eq_of_subset_of_ncard_le hAB
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact hcard


theorem original_pair_four_group_has_nonnested_partner
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ pairOddCore H beta = ⊤)
    (W : Subgroup G) [CFSG.IsElementaryAbelian 2 W] (hcard : Nat.card W = 4)
    (u v : G) (hW : W = Subgroup.closure ({u, v} : Set G))
    (hWB : W ≤ pairPointStabilizer H beta)
    (hzW : z ∈ Subgroup.centralizer (W : Set G))
    (htW : t ∈ Subgroup.centralizer (W : Set G)) :
    ¬ numeratorPairRankPointClass H z v ⊆ numeratorPairRankPointClass H z u ∨
      ¬ numeratorPairRankPointClass H z (u * v) ⊆ numeratorPairRankPointClass H z u := by
  simpa only [numeratorPairRankPointClass_eq_rootFixedSet h] using
    original_pair_generated_four_group_root_centralizer_nonnesting
      hnonab h S hzS hzcenter hbeta ht hgen W hcard u v hW hWB hzW htW

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
