module

public import CFSG.Quasithin.Background.RAVBounds
public import CFSG.Quasithin.Background.B3Four3

public section

namespace CFSG.Quasithin.B3

open scoped commutatorElement

variable {n : ℕ} {k : Mod}


@[expose] def IsFlagSpace (n : ℕ) (k : Mod) (H T : Subgroup (Gp n)) (i : ℕ)
    (W : Subgroup (Mod.V n k)) : Prop :=
  fixV (H.map (Mod.act n k)) ≤ W ∧ Nat.card W = 2 ^ i * Nat.card (fixV (H.map (Mod.act n k))) ∧
    IsTinv T W


theorem normal_subgroupOf_iff {G : Type*} [Group G] {J Y : Subgroup G} (hJY : J ≤ Y) :
    (J.subgroupOf Y).Normal ↔ ∀ x ∈ Y, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
  constructor
  · intro hN x hx j hj
    have h := hN.conj_mem ⟨j, hJY hj⟩ (Subgroup.mem_subgroupOf.2 hj) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.1 h
  · exact normal_subgroupOf_of_conj


@[expose] def FourG (k : Mod) (P : Set (Subgroup (MulAut (Mod.V 6 k))))
    (T R₁ R₂ L₁ L₂ : Subgroup (Gp 6)) (J J₁ : Subgroup (MulAut (Mod.V 6 k))) : Prop :=
  (rk R₂ = 3 ∧ ∀ A : Subgroup (MulAut (Mod.V 6 k)), A ≤ T.map (Mod.act 6 k) →
    (IsStrongFFStarOffender ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) A ↔
      A = R₂.map (Mod.act 6 k))) ∧
  (∀ A : Subgroup (MulAut (Mod.V 6 k)), A ≤ R₁.map (Mod.act 6 k) →
    ¬ IsStrongFFStarOffender ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) A) ∧
  ((∀ A ∈ P, IsStrongFFStarOffender ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) A) →
      J₁ = ⊥ ∧ J = R₂.map (Mod.act 6 k)) ∧
  (J₁ = ⊥ →
    (J ≤ (L₂ ⊔ T).map (Mod.act 6 k) ∧ (J.subgroupOf ((L₂ ⊔ T).map (Mod.act 6 k))).Normal) ∧
    ⁅L₁.map (Mod.act 6 k), J⁆ = ⁅L₁.map (Mod.act 6 k), L₁.map (Mod.act 6 k)⁆) ∧
  (J₁ ≠ ⊥ →
    ⁅L₁.map (Mod.act 6 k), J⁆ = ⁅L₁.map (Mod.act 6 k), L₁.map (Mod.act 6 k)⁆ ∧
    ((∃ τ ∈ R₁, τ.IsSwap ∧ J₁ = (Subgroup.zpowers τ).map (Mod.act 6 k)) ∧
        (J ≤ (L₂ ⊔ T).map (Mod.act 6 k) ∧ (J.subgroupOf ((L₂ ⊔ T).map (Mod.act 6 k))).Normal) ∨
      (J₁ = R₁.map (Mod.act 6 k) ∧ J = T.map (Mod.act 6 k)))) ∧
  ((∀ A ∈ P, Nat.card A = 2) ∨
    ∃ A ∈ P, ∃ B : Subgroup (MulAut (Mod.V 6 k)), B ≤ A ∧ Nat.card A = 2 * Nat.card B ∧
      B ≤ T.map (Mod.act 6 k) ∧ ¬ B ≤ R₂.map (Mod.act 6 k))


@[expose] def IsSylow2In {G : Type*} [Group G] (H T : Subgroup G) : Prop :=
  T ≤ H ∧ IsPGroup 2 T ∧ ¬ 2 ∣ (T.subgroupOf H).index

theorem card_sylow {G : Type*} [Group G] [Finite G] {H S : Subgroup G} (hS : IsSylow2In H S) :
    Nat.card S = 2 ^ padicValNat 2 (Nat.card H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hS.2.1
  have h1 := Subgroup.card_mul_index (S.subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, ha] at h1
  have hm : padicValNat 2 (S.subgroupOf H).index = 0 := padicValNat.eq_zero_of_not_dvd hS.2.2
  have hpos : (S.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← h1, padicValNat.mul (by positivity) hpos, padicValNat.prime_pow, hm, add_zero, ha]

theorem exists_conj_eq_sylow {G : Type*} [Group G] [Finite G] {H T T₀ : Subgroup G}
    (hT : IsSylow2In H T) (hT₀ : IsSylow2In H T₀) : ∃ g ∈ H, cj g T₀ = T := by
  obtain ⟨g, hgH, hle⟩ := exists_conj_le_sylow_sub hT.1 hT.2.1 hT.2.2 hT₀.1 hT₀.2.1
  refine ⟨g, hgH, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [card_sylow hT, show Nat.card (cj g T₀) = Nat.card T₀ from
    Subgroup.card_map_of_injective (MulAut.conj g).injective, card_sylow hT₀]

end CFSG.Quasithin.B3
