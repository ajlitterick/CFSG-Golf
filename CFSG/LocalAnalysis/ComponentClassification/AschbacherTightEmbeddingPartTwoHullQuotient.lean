module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoOddKernelRank

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G] [Finite G]

theorem elementary_Q_le_point_hull (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (E : Subgroup G) (hEQ : E ≤ Q) (hE : IsElemAbelian 2 E) :
    E ≤ involutionPointHull z := by
  intro x hx
  by_cases hone : x = 1
  · exact hone ▸ (involutionPointHull z).one_mem
  · have horder : orderOf x = 2 := orderOf_eq_prime (hE.2 x hx) hone
    apply Subgroup.subset_closure
    rw [← conjugateQInvolutions_eq_pointClass Q hodd hnormal z hzQ hz]
    exact involution_mem_conjugateQInvolutions Q x (hEQ hx) horder

theorem Q_twoRank_le_point_hull (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    twoRank Q ≤ twoRank (involutionPointHull z) := by
  rw [CFSG.ComponentClassification.TwoRankTransport.subgroup,
    CFSG.ComponentClassification.TwoRankTransport.subgroup]
  obtain ⟨E, hEQ, hE, hcard⟩ := CFSG.ComponentClassification.TwoRankTransport.witness Q
  exact CFSG.ComponentClassification.TwoRankTransport.rank_le (involutionPointHull z) E
    (elementary_Q_le_point_hull Q hodd hnormal z hzQ hz E hEQ hE) hE _ hcard


theorem point_hull_odd_core (z : G) :
    oddCore (involutionPointHull z) = (oddCore G).subgroupOf (involutionPointHull z) := by
  let L := involutionPointHull z
  let : L.Normal := by
    change (involutionPointHull z).Normal
    rw [tightly_embedded_point_hull_eq_normalClosure]
    infer_instance
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  exact CFSG.ComponentClassification.OddCore.normal_intersection G L


theorem normal_hull_odd_quotient_point_hull_corefree (Q : Subgroup G)
    (z : G) (hzQ : z ∈ Q) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    let q := QuotientGroup.mk' (oddCore J)
    oddCore (involutionPointHull (q zJ)) = ⊥ := by
  dsimp only
  rw [point_hull_odd_core, normal_hull_odd_quotient_corefree]
  exact Subgroup.bot_subgroupOf _


end CFSG.ComponentClassification.AschbacherTightEmbedding
