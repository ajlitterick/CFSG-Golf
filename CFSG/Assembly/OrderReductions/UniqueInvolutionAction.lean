module

public import CFSG.Assembly.OrderReductions.Helpers
public import CFSG.Assembly.OrderReductions.InvolutionGraph

public section

namespace CFSG.OrderReductions.UniqueInvolutionAction

open CFSG.OrderReductions.InvolutionGraph

theorem distinct_stabilizers_odd_intersection {group points : Type*} [Group group]
    [Finite group] [MulAction group points]
    (unique_fixed : ∀ involution : Involution group,
      ∀ first second : points, involution.val • first = first →
        involution.val • second = second → first = second)
    (first second : points) (distinct : first ≠ second) :
    Odd (Nat.card ↥(MulAction.stabilizer group first ⊓ MulAction.stabilizer group second)) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_contra not_odd
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2
    (Nat.not_odd_iff_even.mp not_odd).two_dvd
  let involution : Involution group :=
    ⟨element.val, by rw [Subgroup.orderOf_coe]; exact element_order⟩
  exact distinct (unique_fixed involution first second element.property.1 element.property.2)

theorem stabilizer_even_of_transitive {group points : Type*} [Group group] [Finite group]
    [MulAction group points] [MulAction.IsPretransitive group points]
    (even_order : Even (Nat.card group))
    (exists_fixed : ∀ involution : Involution group, ∃ point : points,
      involution.val • point = point) (point : points) :
    Even (Nat.card (MulAction.stabilizer group point)) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 even_order.two_dvd
  let involution : Involution group := ⟨element, element_order⟩
  obtain ⟨fixed_point, fixes⟩ := exists_fixed involution
  obtain ⟨conjugator, moves⟩ := MulAction.exists_smul_eq group fixed_point point
  have conjugated_fixed : (conjugator • involution).val • point = point := by
    rw [involution_smul_val, ← moves, mul_smul, mul_smul, inv_smul_smul, fixes]
  apply even_iff_two_dvd.mpr
  rw [← (conjugator • involution).property]
  exact Subgroup.orderOf_dvd_natCard _ conjugated_fixed

theorem stabilizer_ne_top_of_transitive {group points : Type*} [Group group]
    [MulAction group points] [MulAction.IsPretransitive group points] [Nontrivial points]
    (point : points) : MulAction.stabilizer group point ≠ ⊤ := by
  obtain ⟨other, distinct⟩ := exists_ne point
  obtain ⟨element, moves⟩ := MulAction.exists_smul_eq group point other
  intro equal_top
  have fixed : element • point = point := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [equal_top]
    trivial
  exact distinct (moves.symm.trans fixed)

theorem stronglyEmbedded_stabilizer_of_unique_fixed {group points : Type*} [Group group]
    [Finite group] [MulAction group points] [MulAction.IsPretransitive group points]
    [Nontrivial points] (even_order : Even (Nat.card group))
    (unique_fixed : ∀ involution : Involution group, ∃! point : points,
      involution.val • point = point) (point : points) :
    StronglyEmbedded (MulAction.stabilizer group point) := by
  have at_most_one : ∀ involution : Involution group,
      ∀ first second : points, involution.val • first = first →
        involution.val • second = second → first = second := by
    intro involution first second first_fixed second_fixed
    obtain ⟨fixed_point, _, unique⟩ := unique_fixed involution
    exact (unique first first_fixed).trans (unique second second_fixed).symm
  refine ⟨stabilizer_ne_top_of_transitive point,
    stabilizer_even_of_transitive even_order
      (fun involution => (unique_fixed involution).exists) point, ?_⟩
  intro conjugator not_mem
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  apply distinct_stabilizers_odd_intersection at_most_one point (conjugator • point)
  intro equal_points
  exact not_mem equal_points.symm


end CFSG.OrderReductions.UniqueInvolutionAction
