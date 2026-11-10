module

public import CFSG.LocalAnalysis.ComponentClassification.BFailureOddLowerImage
public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoBInclusion
public import CFSG.GroupTheory.CoprimeQuotientNormalizer

public section

namespace CFSG.ComponentClassification.BFailureOdd

open CFSG CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem exists_pComponent_not_le_of_not_badTwo_le {G : Type*} [Group G] {H B : Subgroup G}
    (h : ¬ (badTwoComponentSubgroup H).map H.subtype ≤ B) :
    ∃ L : Subgroup H, IsPComponent 2 L ∧ ¬ IsQuasisimple L ∧ ¬ L.map H.subtype ≤ B := by
  by_contra hcon
  apply h
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  by_contra hLB
  exact hcon ⟨L, hL.1, hL.2, hLB⟩

theorem le_of_isPerfect_of_le_sup {G : Type*} [Group G] {L B N : Subgroup G} [B.Normal]
    [Group.IsPerfect L] [Group.IsSolvable N] (hL : L ≤ B ⊔ N) : L ≤ B := by
  let φ := QuotientGroup.mk' B
  have hLN : L.map φ ≤ N.map φ := by
    have h := Subgroup.map_mono (f := φ) hL
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff B).2 (QuotientGroup.ker_mk' B).ge,
      bot_sup_eq] at h
  have : Group.IsSolvable (N.map φ) := Group.isSolvable_of_surjective (φ.subgroupMap_surjective N)
  have : Group.IsSolvable (L.map φ) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLN)
  have : Group.IsPerfect (L.map φ) := Group.IsPerfect.map φ
  by_contra hne
  have hmap : L.map φ ≠ ⊥ := by
    intro h
    apply hne
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  have : Nontrivial (L.map φ) := (Subgroup.nontrivial_iff_ne_bot _).2 hmap
  exact Group.IsPerfect.not_isSolvable (L.map φ) inferInstance


end CFSG.ComponentClassification.BFailureOdd
