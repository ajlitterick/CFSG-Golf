module

public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched
public import CFSG.ClassicalInvolution.Q3.Q3PBranch

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance

variable {G : Type} [Group G]

theorem isElemAbelian_closure_triple {u v w : G} (hu : u * u = 1) (hv : v * v = 1)
    (hw : w * w = 1) (huv : u * v = v * u) (huw : u * w = w * u) (hvw : v * w = w * v) :
    IsElemAbelian 2 (Subgroup.closure ({u, v, w} : Set G)) := by
  refine Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl <;> assumption
  · intro s hs t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      first | rfl | assumption | exact (by assumption : _ = _).symm

theorem card_closure_triple_eq_eight [Finite G] {z a b : G} (hz : z * z = 1) (ha : a * a = 1)
    (hb : b * b = 1) (hza : z * a = a * z) (hzb : z * b = b * z) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b)
    (hnot : z ∉ Subgroup.closure ({a, b} : Set G)) :
    Nat.card (Subgroup.closure ({z, a, b} : Set G)) = 8 := by
  have hB : Nat.card (Subgroup.closure ({a, b} : Set G)) = 4 :=
    Bootstrap.card_closure_pair_eq_four ha hb ha1 hb1 hne hab
  have hcomm : ∀ s ∈ ({a, b} : Set G), z * s = s * z := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl <;> assumption
  have hle : Nat.card (Subgroup.closure ({z, a, b} : Set G)) ≤ 8 := by
    have := Theorem5.card_closure_insert_le hz hcomm
    rw [hB] at this
    simpa using this
  have hBA : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.closure ({z, a, b} : Set G) :=
    Subgroup.closure_mono (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  have hdvd : 4 ∣ Nat.card (Subgroup.closure ({z, a, b} : Set G)) :=
    hB ▸ Subgroup.card_dvd_of_le hBA
  have hpos : 0 < Nat.card (Subgroup.closure ({z, a, b} : Set G)) := Nat.card_pos
  by_contra h8
  have h4 : Nat.card (Subgroup.closure ({z, a, b} : Set G)) = 4 := by omega
  have hEq := Subgroup.eq_of_le_of_card_ge hBA (by omega)
  exact hnot (hEq ▸ Subgroup.subset_closure (by simp))

theorem IsClassicalMember3.mul_comm_of_mem {L : Subgroup G} {z : G} (h : IsClassicalMember3 L z)
    {l : G} (hl : l ∈ L) : z * l = l * z :=
  h.isCentralInvolution.central l hl


theorem mem_closure_pair_cases {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hba : b * a = a * b := hab.symm
  have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hab' : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, hba, mul_assoc]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> simp
  | one => simp
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [mul_assoc, ha, hb, ha', hab', hba]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl <;> simp [mul_inv_rev, ia, ib, hba]


end CFSG.ClassicalInvolution.Q3
