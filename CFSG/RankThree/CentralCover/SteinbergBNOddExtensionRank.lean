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

include hA hcomm hp hpow


end IsotropicSubgroups

section PowerKernel

variable {P : Type*} [Group P] {A : Subgroup P} {p : ℕ}
  (hA : A ≤ Subgroup.center P) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A) (hpow : ∀ x : P, x ^ p ∈ A)
  (hp : p.Prime) (hp2 : p ≠ 2)


variable [A.Normal]


end PowerKernel

section Statement

variable {P : Type*} [Group P] (A : Subgroup P) [A.Normal] (p : ℕ)

@[expose] def powKerSet : Set P := {x | ∃ a ∈ A, x ^ p = a ^ p}

@[expose] def CentralOddExtensionCaseOne (d : ℕ) : Prop :=
  d = 1 ∧ (∀ x : P, ∃ a ∈ A, x ^ p = a ^ p) ∧ ∀ x : P, (∀ y : P, ⁅x, y⁆ = 1) → x ∈ A

@[expose] def CentralOddExtensionCaseTwo (d : ℕ) : Prop :=
  d = 1 ∧ Nat.card (P ⧸ A) = p * Nat.card ((QuotientGroup.mk : P → P ⧸ A) '' powKerSet A p) ∧
    Nat.card ((QuotientGroup.mk : P → P ⧸ A) '' powKerSet A p) =
      p ^ 2 * Nat.card ((QuotientGroup.mk : P → P ⧸ A) ''
        {x | x ∈ powKerSet A p ∧ ∀ y ∈ powKerSet A p, ⁅x, y⁆ = 1})

@[expose] def CentralOddExtensionCaseThree (d : ℕ) : Prop :=
  d = 2 ∧ (∀ a ∈ A, ∃ x : P, ∃ c ∈ A, a = x ^ p * c ^ p) ∧
    Nat.card ((QuotientGroup.mk : P → P ⧸ A) '' powKerSet A p) = p ^ 2 ∧
    ∃ x ∈ powKerSet A p, ∃ y ∈ powKerSet A p, ⁅x, y⁆ ≠ 1

end Statement


end CFSG.RankThree.CentralCover
