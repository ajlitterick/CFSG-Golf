module

public import CFSG.RankThree.CentralCover.SteinbergBNOddExtensionCore

public section

namespace CFSG.RankThree.CentralCover

open scoped commutatorElement

section IsotropicSubgroups


variable {P : Type*} [Group P] [Finite P] {A : Subgroup P} [A.Normal]
  (hA : A ≤ Subgroup.center P) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A) {p : ℕ} (hp : p.Prime)
  (hpow : ∀ x : P, x ^ p ∈ A)


omit [Finite P] in
include hpow in
theorem quotient_pow_eq_one_of_pow_mem (u : P ⧸ A) : u ^ p = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).2 (hpow x)


omit [Finite P] in
include hp hpow in
theorem card_zpowers_of_ne_one {w : P ⧸ A} (hw : w ≠ 1) : Nat.card (Subgroup.zpowers w) = p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_zpowers, orderOf_eq_prime (quotient_pow_eq_one_of_pow_mem hpow w) hw]


end IsotropicSubgroups

section PowerKernel


end PowerKernel

section Statement


end Statement


end CFSG.RankThree.CentralCover
