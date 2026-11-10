module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.NormalizerClosure
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ElementaryCoordinates
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeSylowTransitivity

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem normal_subgroup_sup_sylow_eq_top_of_pGroup_quotient
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (normalGroup : Subgroup G) (hnormal : normalGroup.Normal)
    (hquotient : IsPGroup prime (G ⧸ normalGroup)) (sylowGroup : Sylow prime G) :
    (sylowGroup : Subgroup G) ⊔ normalGroup = ⊤ := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : normalGroup.Normal := hnormal
  let quotientSylow := sylowGroup.mapSurjective (QuotientGroup.mk'_surjective normalGroup)
  have hquotientTop : (quotientSylow : Subgroup (G ⧸ normalGroup)) = ⊤ := by
    exact (quotientSylow.is_maximal' (hquotient.to_subgroup ⊤) le_top).symm
  have hmap : (sylowGroup : Subgroup G).map (QuotientGroup.mk' normalGroup) = ⊤ := by
    rw [← Sylow.coe_mapSurjective]
    exact hquotientTop
  have hcomap := congrArg (fun subgroup : Subgroup (G ⧸ normalGroup) =>
    subgroup.comap (QuotientGroup.mk' normalGroup)) hmap
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hcomap


theorem exists_maximal_invariant_two_subgroup_containing
    {G : Type*} [Group G] [Finite G] (actingGroup twoGroup : Subgroup G)
    (htwoGroup : IsPGroup 2 twoGroup)
    (hinvariant : actingGroup ≤ Subgroup.normalizer (twoGroup : Set G)) :
    ∃ maximalGroup : Subgroup G, twoGroup ≤ maximalGroup ∧
      rankTwoMaximalInvariantTwoSubgroup actingGroup maximalGroup := by
  obtain ⟨maximalGroup, hinclusion, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun subgroup : Subgroup G => IsPGroup 2 subgroup ∧
      actingGroup ≤ Subgroup.normalizer (subgroup : Set G)) ⟨htwoGroup, hinvariant⟩
  exact ⟨maximalGroup, hinclusion, hmaximal.1.1, hmaximal.1.2,
    fun larger hgroup hnormalized hcontained => le_antisymm
      (hmaximal.2 ⟨hgroup, hnormalized⟩ hcontained) hcontained⟩

end CFSG.RankThreeCoreUniqueness.Helpers
