module

public import CFSG.Quasithin.Background.B4L3Fin

public section

namespace CFSG.Quasithin.L3Fin

open CFSG.Quasithin.L3 Matrix.SpecialLinearGroup

abbrev ent (g : Γ) (i j : Fin 3) : ZMod 2 := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j

set_option maxRecDepth 100000 in
theorem P_mul : ∀ a b : Γ, ent a 1 0 = 0 → ent a 2 0 = 0 → ent b 1 0 = 0 → ent b 2 0 = 0 →
    ent (a * b) 1 0 = 0 ∧ ent (a * b) 2 0 = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem P_inv : ∀ a : Γ, ent a 1 0 = 0 → ent a 2 0 = 0 →
    ent a⁻¹ 1 0 = 0 ∧ ent a⁻¹ 2 0 = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem Q_mul : ∀ a b : Γ, ent a 2 0 = 0 → ent a 2 1 = 0 → ent b 2 0 = 0 → ent b 2 1 = 0 →
    ent (a * b) 2 0 = 0 ∧ ent (a * b) 2 1 = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem Q_inv : ∀ a : Γ, ent a 2 0 = 0 → ent a 2 1 = 0 →
    ent a⁻¹ 2 0 = 0 ∧ ent a⁻¹ 2 1 = 0 := by decide +kernel

@[expose] def subP : Subgroup Γ where
  carrier := {g | ent g 1 0 = 0 ∧ ent g 2 0 = 0}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => P_mul a b ha.1 ha.2 hb.1 hb.2
  inv_mem' := fun {a} ha => P_inv a ha.1 ha.2

@[expose] def subQ : Subgroup Γ where
  carrier := {g | ent g 2 0 = 0 ∧ ent g 2 1 = 0}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => Q_mul a b ha.1 ha.2 hb.1 hb.2
  inv_mem' := fun {a} ha => Q_inv a ha.1 ha.2

instance : DecidablePred (· ∈ subP) := fun g =>
  inferInstanceAs (Decidable (ent g 1 0 = 0 ∧ ent g 2 0 = 0))

instance : DecidablePred (· ∈ subQ) := fun g =>
  inferInstanceAs (Decidable (ent g 2 0 = 0 ∧ ent g 2 1 = 0))

set_option maxRecDepth 100000 in
theorem card_subP : Nat.card subP = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

set_option maxRecDepth 100000 in
theorem card_subQ : Nat.card subQ = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

instance : DecidablePred (· ∈ subP ⊓ subQ) := fun g =>
  inferInstanceAs (Decidable (g ∈ subP ∧ g ∈ subQ))


@[expose] def w12 : Γ := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩

@[expose] def w21 : Γ := ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩

@[expose] def w0 : Γ := ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩

@[expose] def y12 : Γ := transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2)

@[expose] def y23 : Γ := transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : ZMod 2)

@[expose] def y31 : Γ := transvection (show (2 : Fin 3) ≠ 0 by decide) (1 : ZMod 2)


@[expose] def x21 : Γ := transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : ZMod 2)

@[expose] def x32 : Γ := transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : ZMod 2)


set_option maxRecDepth 100000 in
theorem exists_mul_of_not_mem_subP : ∀ g : Γ, g ∈ subP ∨
    ∃ a ∈ Finset.univ.filter (· ∈ subP), x21⁻¹ * (a⁻¹ * g) ∈ subP := by
  unfold x21
  decide +kernel

set_option maxRecDepth 100000 in
theorem exists_mul_of_not_mem_subQ : ∀ g : Γ, g ∈ subQ ∨
    ∃ a ∈ Finset.univ.filter (· ∈ subQ), x32⁻¹ * (a⁻¹ * g) ∈ subQ := by
  unfold x32
  decide +kernel

@[expose] def sw12 : Γ := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩

@[expose] def sw23 : Γ := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩

@[expose] def hsP : Fin 3 → Γ := ![1, x21, sw12]

@[expose] def hsQ : Fin 3 → Γ := ![1, x32, sw23]

theorem hsP_zero : hsP 0 = 1 := rfl

theorem hsQ_zero : hsQ 0 = 1 := rfl

theorem P_two_trans : ∀ g : Γ, g ∈ subP ∨ ∃ a ∈ subP, (hsP 1)⁻¹ * (a⁻¹ * g) ∈ subP := by
  intro g
  rcases exists_mul_of_not_mem_subP g with h | ⟨a, ha, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, (Finset.mem_filter.mp ha).2, h⟩

theorem Q_two_trans : ∀ g : Γ, g ∈ subQ ∨ ∃ a ∈ subQ, (hsQ 1)⁻¹ * (a⁻¹ * g) ∈ subQ := by
  intro g
  rcases exists_mul_of_not_mem_subQ g with h | ⟨a, ha, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, (Finset.mem_filter.mp ha).2, h⟩

set_option maxRecDepth 100000 in
theorem P_distinct : ∀ i j : Fin 3, (hsP i)⁻¹ * hsP j ∈ subP → i = j := by
  unfold hsP x21 sw12; decide +kernel

set_option maxRecDepth 100000 in
theorem Q_distinct : ∀ i j : Fin 3, (hsQ i)⁻¹ * hsQ j ∈ subQ → i = j := by
  unfold hsQ x32 sw23; decide +kernel

set_option maxRecDepth 100000 in
theorem P_closed : ∀ q : Γ, q ∈ subQ → ∀ i : Fin 3,
    ∃ j : Fin 3, (hsP j)⁻¹ * (q * hsP i) ∈ subP := by
  unfold hsP x21 sw12; decide +kernel

set_option maxRecDepth 100000 in
theorem Q_closed : ∀ q : Γ, q ∈ subP → ∀ i : Fin 3,
    ∃ j : Fin 3, (hsQ j)⁻¹ * (q * hsQ i) ∈ subQ := by
  unfold hsQ x32 sw23; decide +kernel

set_option maxRecDepth 100000 in
theorem P_not_conj : ∀ g : Γ, ∃ a : Γ, a ∈ subP ∧ g * a * g⁻¹ ∉ subQ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem Q_not_conj : ∀ g : Γ, ∃ a : Γ, a ∈ subQ ∧ g * a * g⁻¹ ∉ subP := by
  decide +kernel


end CFSG.Quasithin.L3Fin
