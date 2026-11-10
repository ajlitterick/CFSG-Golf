module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigH

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient} {N K K' : Subgroup G}

theorem exists_isKleinFour_le {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) : ∃ E : Subgroup G, E ≤ B ∧ IsKleinFour E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) 2 (n := 2)
    (by rw [hB8]; norm_num)
  refine ⟨E₀.map B.subtype, map_subtype_le _, isKleinFour_of_card_eq_four ?_ ?_⟩
  · rw [card_map_of_injective B.subtype_injective, hE₀]; norm_num
  · rintro _ ⟨x, -, rfl⟩
    exact hB.2 x x.2

theorem isPGroup_sup_of_le_centralizer {B V : Subgroup G} (hB2 : IsPGroup 2 B)
    (hV2 : IsPGroup 2 V) (hBV : B ≤ centralizer (V : Set G)) : IsPGroup 2 (B ⊔ V : Subgroup G) :=
  IsPGroup.to_sup_of_normal_right' hB2 hV2
    (hBV.trans (Subgroup.centralizer_le_normalizer (V : Set G)))


end CFSG.ComponentClassification.Sol76.Sig
