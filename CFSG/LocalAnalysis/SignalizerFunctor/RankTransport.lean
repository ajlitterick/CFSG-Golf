module

public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryComplements
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem cardinality_sup_of_disjoint_commutative
    {GroupType : Type groupUniverse} [CommGroup GroupType]
    (first second : Subgroup GroupType) (disjoint : Disjoint first second) :
    Nat.card (first ⊔ second : Subgroup GroupType) = Nat.card first * Nat.card second := by
  let combined : Subgroup GroupType := first ⊔ second
  let firstInternal := first.subgroupOf combined
  let secondInternal := second.subgroupOf combined
  have internal_disjoint : Disjoint firstInternal secondInternal := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro element member
    change element = 1
    apply Subtype.ext
    have ambient_member : element.val ∈ first ⊓ second := member
    rw [disjoint.eq_bot] at ambient_member
    exact ambient_member
  have internal_whole : firstInternal ⊔ secondInternal = ⊤ := by
    apply top_unique
    intro element _
    obtain ⟨firstElement, first_member, secondElement, second_member, product⟩ :=
      Subgroup.mem_sup.mp element.property
    apply Subgroup.mem_sup.mpr
    refine ⟨⟨firstElement, Subgroup.mem_sup_left first_member⟩, first_member,
      ⟨secondElement, Subgroup.mem_sup_right second_member⟩, second_member, ?_⟩
    exact Subtype.ext product
  have complementary : IsCompl firstInternal secondInternal :=
    ⟨internal_disjoint, codisjoint_iff.mpr internal_whole⟩
  have cardinality := (isComplement'_of_isCompl_commutative complementary).card_mul_card
  have first_card : Nat.card firstInternal = Nat.card first :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show first ≤ combined from le_sup_left)).toEquiv
  have second_card : Nat.card secondInternal = Nat.card second :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show second ≤ combined from le_sup_right)).toEquiv
  rw [first_card, second_card] at cardinality
  exact cardinality.symm


end CFSG.SignalizerFunctor.Helpers
