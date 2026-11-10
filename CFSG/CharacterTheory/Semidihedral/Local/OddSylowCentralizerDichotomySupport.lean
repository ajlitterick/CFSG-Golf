module

public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

universe u

variable {G : Type u} [Group G]

section Basics

theorem odd_card_N [Finite G] (t : G) : Odd (Nat.card (N t)) :=
  Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))

theorem card_Z (t : G) (ht : orderOf t = 2) : Nat.card (Z t) = 2 := by
  rw [Nat.card_zpowers, tInC, Subgroup.orderOf_mk, ht]

theorem Z_le_centralizer (t : G) (X : Set (C t)) : Z t ≤ Subgroup.centralizer X := by
  rw [Subgroup.zpowers_le]
  exact Subgroup.center_le_centralizer X (tInC_central t)


end Basics

section TwoParts

variable [Finite G]

theorem factorization_two_card_eq {n : ℕ} (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0) : (Nat.card G).factorization 2 = n := by
  have hS0 : Nat.card S0 = 2 ^ n := by
    rw [← Nat.card_congr f0.toEquiv, card n (by omega)]
  have hcop := S0.card_coprime_index
  have hidx : ¬ 2 ∣ (S0 : Subgroup G).index := by
    intro h
    have h1 : 2 ∣ Nat.card S0 := by rw [hS0]; exact dvd_pow_self 2 (by omega)
    have := Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.coprime_dvd_right h hcop)
    norm_num at this
  have hidx0 : (S0 : Subgroup G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← Subgroup.card_mul_index (S0 : Subgroup G), Nat.factorization_mul (by rw [hS0]; positivity)
    hidx0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  change (Nat.card S0).factorization 2 = n
  rw [hS0, Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self, smul_eq_mul,
    mul_one]


end TwoParts

section Dichotomy


end Dichotomy

end CFSG.Semidihedral.Local
