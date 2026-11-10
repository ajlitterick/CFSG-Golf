module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXCyclic
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FinalTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace L45RankX

section Sylow

variable {G : Type*} [Group G] [Finite G]


end Sylow

section Lift

variable {G : Type*} [Group G] {K : Subgroup G} {R : Type} [Group R]
  {θ : K ⧸ Subgroup.center K ≃* R}

theorem exists_lift_of_coprime {p : ℕ} (hp : p.Prime)
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center K))) {r : R} {m : ℕ} (hr : r ^ p ^ m = 1) :
    ∃ k : K, k ^ p ^ m = 1 ∧ θ (k : K ⧸ Subgroup.center K) = r := by
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H k₀ =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨1, one_pow _, ?_⟩
      rw [pow_zero, pow_one] at hr
      rw [hr, QuotientGroup.mk_one, map_one]
    set N := Nat.card (Subgroup.center K) with hN
    have hcop : Nat.Coprime N (p ^ m) := (Nat.Coprime.pow_left m hZ).symm
    obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
      (Nat.one_lt_pow hm.ne' hp.one_lt)
    have h1 : k₀ ^ p ^ m ∈ Subgroup.center K := by
      have : ((k₀ : K ⧸ Subgroup.center K)) ^ p ^ m = 1 :=
        θ.injective (by rw [map_pow, hr, map_one])
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
      exact this
    have h2 : (k₀ ^ p ^ m) ^ N = 1 := by
      have := pow_card_eq_one' (G := Subgroup.center K) (x := ⟨_, h1⟩)
      exact congrArg Subtype.val this
    refine ⟨k₀ ^ (N * j), ?_, ?_⟩
    · calc (k₀ ^ (N * j)) ^ p ^ m = ((k₀ ^ p ^ m) ^ N) ^ j := by
            rw [← pow_mul, ← pow_mul, ← pow_mul]
            congr 1
            ring
        _ = 1 := by rw [h2, one_pow]
    · rw [QuotientGroup.mk_pow, map_pow]
      exact pow_eq_self_of_mod_eq_one hr hj


end Lift

end L45RankX


section Config


end Config


end CFSG.StandardType
