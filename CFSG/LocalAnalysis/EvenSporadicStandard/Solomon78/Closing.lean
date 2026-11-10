module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Sylow

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {t u : G}

omit [Finite G] in
theorem center_eq_bot_of_simple_nonabelian {X : Type} [Group X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h' | h'
  · exact h'
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd (mem_center_iff.1 (h' ▸ mem_top b) a) hab


omit [Finite G] in
theorem not_mem_of_center_eq_bot (htC : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hZ : center L = ⊥) : t ∉ L := by
  intro htL
  have hmem : t ∈ (center L).map L.subtype := by
    rw [map_center_eq_inf_centralizer]
    exact ⟨htL, htC⟩
  rw [hZ, Subgroup.map_bot, mem_bot] at hmem
  exact ne_one_of_orderOf_eq_two ht2 hmem


end CFSG.EvenSporadicStandard.Solomon78
