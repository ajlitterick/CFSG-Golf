module

public import CFSG.Foundations.Basic

public section

namespace CFSG

open Subgroup

variable (S : Type*) [Group S]

@[expose] def higherElemThompsonFamily (j : ℕ) : Set (Subgroup S) :=
  {A | IsElementaryAbelian 2 A ∧ pRank 2 A = pRank 2 S - j}

@[expose] def higherElemThompson (j : ℕ) : Subgroup S :=
  sSup (higherElemThompsonFamily S j)

variable {S}

@[expose] def omegaOneCenter (J : Subgroup S) : Subgroup S where
  carrier := {z | z ∈ (center J).map J.subtype ∧ z ^ 2 = 1}
  one_mem' := ⟨one_mem _, one_pow 2⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a, ha, rfl⟩, hap⟩ ⟨⟨b, hb, rfl⟩, hbp⟩
    refine ⟨mul_mem (mem_map_of_mem _ ha) (mem_map_of_mem _ hb), ?_⟩
    have hab : Commute (a : S) b :=
      (show Commute b a from mem_center_iff.mp ha b).symm.map J.subtype
    change (a : S) ^ 2 = 1 at hap
    change (b : S) ^ 2 = 1 at hbp
    change ((a : S) * b) ^ 2 = 1
    rw [hab.mul_pow, hap, hbp, one_mul]
  inv_mem' := by
    rintro _ ⟨hz, hzp⟩
    exact ⟨inv_mem hz, by rw [inv_pow, hzp, inv_one]⟩

variable (S) in
@[expose] def higherElemThompsonOmega (j : ℕ) : Subgroup S :=
  omegaOneCenter (higherElemThompson S j)


theorem pRank_eq_of_card_eq_pow {A : Type*} [Group A] [Finite A] {p k : ℕ} (hp : 1 < p)
    [IsElementaryAbelian p A] (hk : Nat.card A = p ^ k) : pRank p A = k := by
  have htop : IsElementaryAbelian p (⊤ : Subgroup A) :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (mul_comm' (a : A) b)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p A) (x : A)) }
  have hbound : ∀ r ∈ {r : ℕ | ∃ B : Subgroup A, IsElementaryAbelian p B ∧ Nat.card B = p ^ r},
      r ≤ k := by
    rintro r ⟨B, -, hB⟩
    have h := Subgroup.card_le_card_group B
    rw [hB, hk] at h
    exact (Nat.pow_le_pow_iff_right hp).mp h
  have hmem : k ∈ {r : ℕ | ∃ B : Subgroup A, IsElementaryAbelian p B ∧ Nat.card B = p ^ r} :=
    ⟨⊤, htop, by rw [Subgroup.card_top, hk]⟩
  exact le_antisymm (csSup_le ⟨k, hmem⟩ hbound) (le_csSup ⟨k, hbound⟩ hmem)

theorem mem_higherElemThompsonFamily_iff [Finite S] (j : ℕ) (A : Subgroup S) :
    A ∈ higherElemThompsonFamily S j ↔
      IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ (pRank 2 S - j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨hA, hrank⟩
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    refine ⟨hA, ?_⟩
    rw [hk, ← hrank, pRank_eq_of_card_eq_pow one_lt_two hk]
  · rintro ⟨hA, hcard⟩
    exact ⟨hA, pRank_eq_of_card_eq_pow one_lt_two hcard⟩

variable (S)

theorem higherElemThompson_zero [Finite S] : higherElemThompson S 0 = elemThompson S 2 := by
  unfold higherElemThompson elemThompson
  congr 1
  ext A
  rw [mem_higherElemThompsonFamily_iff, Nat.sub_zero]
  rfl


end CFSG
