module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoQuotientClass

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G] [Finite G]

theorem normal_hull_odd_quotient_point_hull_split_second_equiv (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) (hrank : 2 ≤ twoRank Q)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    {A B : Type*} [Group A] [IsMulCommutative A] [Group B]
    (e :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      let q := QuotientGroup.mk' (oddCore J)
      involutionPointHull (q zJ) ≃* A × B) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    let q := QuotientGroup.mk' (oddCore J)
    ∃ e' : involutionPointHull (q zJ) ≃* B, ∀ x, e' x = (e x).2 := by
  let J := Subgroup.normalClosure (Q : Set G)
  let QJ := Q.subgroupOf J
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let q := QuotientGroup.mk' (oddCore J)
  have hrankJ : 2 ≤ twoRank QJ := by
    rw [normal_hull_Q_twoRank]
    exact hrank
  exact point_hull_image_split_second_equiv QJ
    (normal_hull_Q_odd_normalizer_overlaps Q htight hodd)
    (normal_hull_Q_nonnormal Q htight hodd hnormal) hrankJ zJ hzQ
    ((Subgroup.orderOf_coe zJ).symm.trans hz) q
    (normal_hull_odd_quotient_surjective Q) e

theorem normal_hull_odd_quotient_point_hull_strong_embedding_of_split
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) (hrank : 2 ≤ twoRank Q)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    {A B : Type*} [Group A] [IsMulCommutative A] [Group B] [Finite B]
    (e :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      let q := QuotientGroup.mk' (oddCore J)
      involutionPointHull (q zJ) ≃* A × B)
    (M : Subgroup B) (hM : fusionStronglyEmbedded M)
    (hmember :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      let q := QuotientGroup.mk' (oddCore J)
      ∀ x : involutionPointHull (q zJ),
        (e x).2 ∈ M ↔ (x : J ⧸ oddCore J) ∈
          Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J))) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    let q := QuotientGroup.mk' (oddCore J)
    fusionStronglyEmbedded
      ((Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J))).subgroupOf
        (involutionPointHull (q zJ))) := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let q := QuotientGroup.mk' (oddCore J)
  let Hq := Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J))
  let Lq := involutionPointHull (q zJ)
  obtain ⟨e', he'⟩ := normal_hull_odd_quotient_point_hull_split_second_equiv
    Q htight hodd hnormal hrank z hzQ hz e
  have hmap : M.map e'.symm.toMonoidHom = Hq.subgroupOf Lq := by
    ext x
    constructor
    · rintro ⟨b, hb, hbx⟩
      have hexb : e' x = b := by
        rw [← hbx]
        exact e'.apply_symm_apply b
      apply (hmember x).mp
      rw [← he' x, hexb]
      exact hb
    · intro hx
      refine ⟨e' x, ?_, e'.symm_apply_apply x⟩
      rw [he' x]
      exact (hmember x).mpr hx
  change fusionStronglyEmbedded (Hq.subgroupOf Lq)
  rw [← hmap]
  exact hM.map_mulEquiv e'.symm


end CFSG.ComponentClassification.AschbacherTightEmbedding
