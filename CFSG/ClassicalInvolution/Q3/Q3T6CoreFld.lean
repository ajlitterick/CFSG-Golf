module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutNorm
public import CFSG.ClassicalInvolution.Asc77.AscE184Quot

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups Pointwise

section Generic


end Generic

section Action

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}
  (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))


end Action

section Counting

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem natCard_sylow_eq_eight (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))
    {R : Subgroup G} (hR : IsSylow2In R K) : Nat.card R = 8 := by
  have hK : Nat.card K = 24 * Nat.card (classicalInvolutionOddCore K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore K),
      Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hodd : Odd (Nat.card (classicalInvolutionOddCore K)) :=
    CFSG.ComponentClassification.OddCore.odd_card K
  have h2 : ¬ 2 ∣ Nat.card (classicalInvolutionOddCore K) := by
    rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  rw [natCard_eq_pow_of_isSylow2In hR, hK,
    Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h2]
  have : (24 : ℕ).factorization 2 = 3 := by
    rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization Nat.prime_three]
    simp
  rw [this]
  norm_num


end Counting

end CFSG.ClassicalInvolution.Q3.Q3T6
