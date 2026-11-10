module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalHallConfinement
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers


theorem pGroup_proper_subgroup_lt_internal_normalizer
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (primeGroup subgroup : Subgroup G) (hpGroup : IsPGroup prime primeGroup)
    (hproper : subgroup < primeGroup) :
    subgroup < primeGroup ⊓ Subgroup.normalizer (subgroup : Set G) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Group.IsNilpotent primeGroup := hpGroup.isNilpotent
  have hinternalProper : subgroup.subgroupOf primeGroup < ⊤ := by
    exact lt_top_iff_ne_top.mpr (fun htop =>
      hproper.not_ge (Subgroup.subgroupOf_eq_top.mp htop))
  have hinternal := Group.normalizerCondition_of_isNilpotent
    (subgroup.subgroupOf primeGroup) hinternalProper
  have hmapped := Subgroup.map_subtype_lt_map_subtype.mpr hinternal
  rw [Subgroup.map_subgroupOf_eq_of_le hproper.le,
    ← Subgroup.subgroupOf_normalizer_eq hproper.le] at hmapped
  have hnormalizerMap : Subgroup.map primeGroup.subtype
      ((Subgroup.normalizer (subgroup : Set G)).subgroupOf primeGroup) =
      primeGroup ⊓ Subgroup.normalizer (subgroup : Set G) := by
    rw [← Subgroup.inf_subgroupOf_right, Subgroup.map_subgroupOf_eq_of_le inf_le_right,
      inf_comm]
  rwa [hnormalizerMap] at hmapped

theorem invariant_normalizer_intersection
    {G : Type*} [Group G] (actingGroup first second : Subgroup G)
    (hfirst : actingGroup ≤ Subgroup.normalizer (first : Set G))
    (hsecond : actingGroup ≤ Subgroup.normalizer (second : Set G)) :
    actingGroup ≤ Subgroup.normalizer
      ((first ⊓ Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have hintersection := common_normalizer_le_normalizer_inf actingGroup first second hfirst hsecond
  have hnormalizer := hintersection.trans
    (Subgroup.le_normalizer (H := Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G)))
  exact common_normalizer_le_normalizer_inf actingGroup _ _ hfirst hnormalizer


theorem maximal_pair_intersection_normalizer_twoLocal
    {G : Type*} [Group G] (actingGroup first second : Subgroup G)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup second)
    (hnontrivial : first ⊓ second ≠ ⊥) :
    IsTwoLocal (Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G)) ∧
      actingGroup ≤ Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G) :=
  ⟨⟨_, hnontrivial, hfirst.1.to_inf_left, rfl⟩,
    common_normalizer_le_normalizer_inf actingGroup first second hfirst.2.1 hsecond.2.1⟩


end CFSG.RankThreeCoreUniqueness.Helpers
