module

public import CFSG.Assembly.OrderReductions.SolvableComplementContainment
public import CFSG.Assembly.OrderReductions.PrimeRegular

public section

namespace CFSG.OrderReductions.RegularCore

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.InvolutiveIntersection
open CFSG.OrderReductions.PrimeComplementCore

theorem ambientCore_invariant {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (subgroup : Subgroup group) (invariant : subgroup.map automorphism.toMonoidHom = subgroup) :
    (ambientCore prime subgroup).map automorphism.toMonoidHom = ambientCore prime subgroup := by
  rw [ambientCore_map_equiv, invariant]

theorem intersection_core_le {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (subgroup : Subgroup group) [Group.IsSolvable subgroup]
    (full_primePart : CFSG.OrderReductions.PrimePart.primePart prime
      (Nat.card (intersection automorphism subgroup)) =
        CFSG.OrderReductions.PrimePart.primePart prime (Nat.card subgroup)) :
    ambientCore prime (intersection automorphism subgroup) ≤ ambientCore prime subgroup :=
  CFSG.OrderReductions.SolvableComplementContainment.full_primePart_ambientCore_le prime _ _
    inf_le_left full_primePart

theorem core_invariant_of_equal_intersection {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) (subgroup : Subgroup group)
    (core_eq : ambientCore prime (intersection automorphism subgroup) = ambientCore prime subgroup) :
    (ambientCore prime subgroup).map automorphism.toMonoidHom = ambientCore prime subgroup := by
  rw [← core_eq]
  exact ambientCore_invariant prime automorphism _ (intersection_invariant automorphism involutive subgroup)

theorem regular_pair_intersection_core_le {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group)
    (distinct : first ≠ second)
    [Group.IsSolvable (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)]
    (regular : CFSG.OrderReductions.PrimeRegular.PRegular prime
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) (componentStabilizer first))
    (involution : Involution group) (mem_first : involution.val ∈ componentStabilizer first) :
    ambientCore prime (intersection (MulAut.conj involution.val)
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)) ≤
        ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) := by
  exact intersection_core_le prime (MulAut.conj involution.val) _
    ((CFSG.OrderReductions.PrimeRegular.pRegular_pair_iff_every_involution
      prime first second distinct).mp regular involution mem_first)


theorem characteristic_pair_image_normalizes {group : Type*} [Group group]
    (pair : Subgroup group) (characteristic : Subgroup pair) [characteristic.Characteristic]
    (element : group) (normalizes : element ∈ Subgroup.normalizer (pair : Set group)) :
    element ∈ Subgroup.normalizer (characteristic.map pair.subtype : Set group) := by
  exact CFSG.OrderReductions.TwoPointSylow.normalizes_image_of_invariant pair element normalizes characteristic
    (Subgroup.characteristic_iff_map_eq.mp inferInstance (pair.normalizerMonoidHom ⟨element, normalizes⟩))

end CFSG.OrderReductions.RegularCore
