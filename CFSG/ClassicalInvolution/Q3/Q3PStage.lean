module

public import CFSG.ClassicalInvolution.Q3.Q3PBranch

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G]

theorem card_closure_pair_le_four [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 4 := by
  classical
  have hba : b * a = a * b := hab.symm
  have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hab' : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, hba, mul_assoc]
  have hsub : ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) ⊆
      (({1, a, b, a * b} : Finset G) : Set G) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
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
  calc Nat.card (Subgroup.closure ({a, b} : Set G))
      = Nat.card ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) := rfl
    _ ≤ Nat.card (({1, a, b, a * b} : Finset G) : Set G) := Nat.card_mono (Set.toFinite _) hsub
    _ = Finset.card ({1, a, b, a * b} : Finset G) := Nat.card_eq_finsetCard _
    _ ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp

theorem card_closure_triple_le_four [Finite G] {u v w : G} (hu : u * u = 1) (hv : v * v = 1)
    (hw : w * w = 1) (huv : u * v = v * u) (huw : u * w = w * u) (hvw : v * w = w * v)
    (hdep : u = v ∨ u = w ∨ v = w ∨ u * v = w) :
    Nat.card (Subgroup.closure ({u, v, w} : Set G)) ≤ 4 := by
  have mem : ∀ {a b : G} {x : G}, x = a ∨ x = b → x ∈ Subgroup.closure ({a, b} : Set G) := by
    rintro a b x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  rcases hdep with h | h | h | h
  ·
    have hle : Subgroup.closure ({u, v, w} : Set G) ≤ Subgroup.closure ({u, w} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem (Or.inl rfl)
      · exact mem (Or.inl h.symm)
      · exact mem (Or.inr rfl)
    exact (Subgroup.card_le_of_le hle).trans (card_closure_pair_le_four hu hw huw)
  ·
    have hle : Subgroup.closure ({u, v, w} : Set G) ≤ Subgroup.closure ({u, v} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem (Or.inl rfl)
      · exact mem (Or.inr rfl)
      · exact mem (Or.inl h.symm)
    exact (Subgroup.card_le_of_le hle).trans (card_closure_pair_le_four hu hv huv)
  ·
    have hle : Subgroup.closure ({u, v, w} : Set G) ≤ Subgroup.closure ({u, v} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem (Or.inl rfl)
      · exact mem (Or.inr rfl)
      · exact mem (Or.inr h.symm)
    exact (Subgroup.card_le_of_le hle).trans (card_closure_pair_le_four hu hv huv)
  ·
    have hle : Subgroup.closure ({u, v, w} : Set G) ≤ Subgroup.closure ({u, v} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem (Or.inl rfl)
      · exact mem (Or.inr rfl)
      · rw [← h]
        exact mul_mem (mem (Or.inl rfl)) (mem (Or.inr rfl))
    exact (Subgroup.card_le_of_le hle).trans (card_closure_pair_le_four hu hv huv)


end CFSG.ClassicalInvolution.Q3
