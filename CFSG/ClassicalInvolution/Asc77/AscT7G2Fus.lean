module

public import CFSG.ClassicalInvolution.Asc77.AscT7G2Fin
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Trans
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Frat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected


variable (p f : ℕ) [Fact p.Prime]


variable {p f}

namespace T7G2

open T7F2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem relIndex_B {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ t' : G}
    (hT : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')) :
    (R ⊔ R' ⊔ Subgroup.zpowers t').relIndex (S : Subgroup G) = 2 := by
  have hRRN : R ⊔ R' ≤ Nsub S R := sup_le hT.R_le_N hT.R'_le_N
  have ht'n : t' ∉ R ⊔ R' := fun hmem => hT.t'_not_mem_N (hRRN hmem)
  have ht1 : t' ≠ 1 := fun h1 => ht'n (h1 ▸ (R ⊔ R').one_mem)
  have hz2 : orderOf t' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hT.ht'2) ht1
  have hnorm : Subgroup.zpowers t' ≤ Subgroup.normalizer ((R ⊔ R' : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    exact conj_mem_RR hT hT.ht'S hx |> fun h1 => by simpa [hT.ht'inv] using h1
  have hinf : (R ⊔ R') ⊓ Subgroup.zpowers t' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hx1, k, hk⟩
    simp only at hk
    subst hk
    have hzz : t' ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hT.ht'2
    obtain ⟨m, hm⟩ := Int.even_or_odd' k
    rcases hm with rfl | rfl
    · rw [zpow_mul, hzz, one_zpow]
    · exfalso
      apply ht'n
      have : t' ^ (2 * m + 1) = t' := by
        rw [zpow_add, zpow_mul, hzz, one_zpow, one_mul, zpow_one]
      rwa [this] at hx1
  have hprod := T7A.card_sup_mul_card_inf hnorm
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hz2, mul_one, sup_comm] at hprod
  have hBS : R ⊔ R' ⊔ Subgroup.zpowers t' ≤ (S : Subgroup G) :=
    sup_le (sup_le hT.hRS hT.hR'S) (Subgroup.zpowers_le.mpr hT.ht'S)
  have h2 := Subgroup.relIndex_mul_card (R ⊔ R' ⊔ Subgroup.zpowers t') (S : Subgroup G)
  rw [inf_eq_left.mpr hBS, hprod, h4] at h2
  have hρ : 0 < Nat.card ↥(R ⊔ R') := Nat.card_pos
  have : (R ⊔ R' ⊔ Subgroup.zpowers t').relIndex (S : Subgroup G) * (Nat.card ↥(R ⊔ R') * 2) =
      2 * (Nat.card ↥(R ⊔ R') * 2) := by rw [h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this


end T7G2

end CFSG.ClassicalInvolution.Asc77
