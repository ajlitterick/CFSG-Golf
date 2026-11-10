module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.Open.OrderForm

public section

open CFSG.Open

namespace CFSG.OrderReductions.Helpers


theorem prime_card_of_simple_commutative (group : Type*) [Group group]
    [IsSimpleGroup group] [IsMulCommutative group] : (Nat.card group).Prime :=
  Group.is_simple_iff_prime_card.mp inferInstance


theorem simple_solvable_isMulCommutative (group : Type*) [Group group]
    [IsSimpleGroup group] [Group.IsSolvable group] : IsMulCommutative group :=
  IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance)

theorem prime_card_of_simple_solvable (group : Type*) [Group group]
    [IsSimpleGroup group] [Group.IsSolvable group] : (Nat.card group).Prime := by
  let := simple_solvable_isMulCommutative group
  exact prime_card_of_simple_commutative group


theorem simple_noncommutative_isPerfect (group : Type*) [Group group]
    [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group) :
    Group.IsPerfect group := by
  apply Group.IsPerfect.mk
  rcases CFSG.eq_bot_or_eq_top_of_normal (commutator group) inferInstance with
    commutator_bot | commutator_top
  · exact False.elim (noncommutative ((commutator_eq_bot_iff group).mp commutator_bot))
  · exact commutator_top

theorem simple_noncommutative_center_eq_bot (group : Type*) [Group group]
    [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group) :
    Subgroup.center group = ⊥ := by
  rcases CFSG.eq_bot_or_eq_top_of_normal (Subgroup.center group) inferInstance with
    center_bot | center_top
  · exact center_bot
  · exact False.elim (noncommutative (Subgroup.center_eq_top_iff.mp center_top))


theorem prime_card_of_simple_prime_power (group : Type*) [Group group] [Finite group]
    [IsSimpleGroup group] (prime_power_order : IsPrimePow (Nat.card group)) :
    (Nat.card group).Prime := by
  obtain ⟨prime, exponent, prime_prime, _, order_eq⟩ :=
    (isPrimePow_nat_iff (Nat.card group)).mp prime_power_order
  have : Fact prime.Prime := ⟨prime_prime⟩
  have : Group.IsNilpotent group := (IsPGroup.of_card order_eq.symm).isNilpotent
  exact prime_card_of_simple_solvable group


theorem prime_card_of_simple_squarefree (group : Type*) [Group group] [Finite group]
    [IsSimpleGroup group] (squarefree_order : Squarefree (Nat.card group)) :
    (Nat.card group).Prime := by
  let := IsZGroup.of_squarefree squarefree_order
  exact prime_card_of_simple_solvable group


theorem perfect_hom_to_commutative_eq_one (group : Type*) [Group group]
    [Group.IsPerfect group] (target : Type*) [CommGroup target]
    (homomorphism : group →* target) : homomorphism = 1 := by
  apply MonoidHom.ker_eq_top_iff.mp
  exact top_unique (by
    rw [← Group.IsPerfect.commutator_eq_top (G := group)]
    exact Abelianization.commutator_subset_ker homomorphism)

theorem perfect_minFac_sylow_not_cyclic (group : Type*) [Group group] [Finite group]
    [Nontrivial group] [Group.IsPerfect group]
    (sylow : Sylow (Nat.card group).minFac group) :
    ¬ IsCyclic sylow := by
  intro cyclic
  have order_ne_one : Nat.card group ≠ 1 := by
    intro order_one
    have := (Nat.card_eq_one_iff_unique.mp order_one).1
    exact not_subsingleton group inferInstance
  have prime : (Nat.card group).minFac.Prime := Nat.minFac_prime order_ne_one
  have : Fact (Nat.card group).minFac.Prime := ⟨prime⟩
  let normalizer_inclusion := cyclic.normalizer_le_centralizer rfl
  let transfer := MonoidHom.transferSylow sylow normalizer_inclusion
  let := cyclic
  let _ : CommGroup sylow := IsMulCommutative.instCommGroup
  have transfer_trivial : transfer = 1 :=
    perfect_hom_to_commutative_eq_one group sylow transfer
  have kernel_top : transfer.ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr transfer_trivial
  have not_dvd_kernel := MonoidHom.not_dvd_card_ker_transferSylow sylow normalizer_inclusion
  apply not_dvd_kernel
  change (Nat.card group).minFac ∣ Nat.card transfer.ker
  rw [kernel_top, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup group) ≃* group).toEquiv]
  exact Nat.minFac_dvd (Nat.card group)

theorem perfect_minFac_sq_dvd_card (group : Type*) [Group group] [Finite group]
    [Nontrivial group] [Group.IsPerfect group] :
    (Nat.card group).minFac ^ 2 ∣ Nat.card group := by
  have order_ne_one : Nat.card group ≠ 1 := by
    intro order_one
    have := (Nat.card_eq_one_iff_unique.mp order_one).1
    exact not_subsingleton group inferInstance
  have prime : (Nat.card group).minFac.Prime := Nat.minFac_prime order_ne_one
  have : Fact (Nat.card group).minFac.Prime := ⟨prime⟩
  have exponent_pos : 0 < (Nat.card group).factorization (Nat.card group).minFac :=
    prime.factorization_pos_of_dvd Nat.card_pos.ne' (Nat.minFac_dvd (Nat.card group))
  apply (prime.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr
  by_contra exponent_small
  have exponent_one : (Nat.card group).factorization (Nat.card group).minFac = 1 := by
    omega
  obtain ⟨sylow⟩ : Nonempty (Sylow (Nat.card group).minFac group) := inferInstance
  apply perfect_minFac_sylow_not_cyclic group sylow
  apply isCyclic_of_prime_card (p := (Nat.card group).minFac)
  simpa only [exponent_one, pow_one] using sylow.card_eq_multiplicity


theorem simple_noncommutative_minFac_sq_dvd_card (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group) :
    (Nat.card group).minFac ^ 2 ∣ Nat.card group := by
  let := simple_noncommutative_isPerfect group noncommutative
  exact perfect_minFac_sq_dvd_card group


end CFSG.OrderReductions.Helpers
