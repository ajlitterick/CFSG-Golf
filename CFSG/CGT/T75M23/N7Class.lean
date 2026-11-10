module

public import CFSG.CGT.T75M23.A7Gens

public section

namespace CFSG.CGT.T75M23

open CFSG.CGT.T75JM

@[expose] def modelX7 : Cols := ⟨9, 10, 15, 8⟩

@[expose] def modelY7 : Cols := ⟨2, 6, 10, 3⟩

@[expose] def RelC7 (X Y : Cols) : Prop :=
  compC X X = idC ∧ X ≠ idC ∧ powC Y 5 = idC ∧
    powC (compC X (compC Y (compC X (powC Y 4)))) 3 = idC ∧
    powC (compC (powC Y 4) X) 7 = idC ∧
    compC X (compC Y (compC X (compC (powC (compC Y (compC X (compC (powC Y 4)
      (compC X Y)))) 2) (compC Y (compC X (powC Y 4)))))) = idC

instance (X Y : Cols) : Decidable (RelC7 X Y) := by unfold RelC7; infer_instance

@[expose] def EquivData7 (X Y Q Qi : Cols) : Prop :=
  (∀ i, Q.col i < 16) ∧ (∀ i, Qi.col i < 16) ∧ compC Qi Q = idC ∧ compC Q Qi = idC ∧
    compC X Q = compC Q modelX7 ∧ compC Y Q = compC Q modelY7

@[expose] def EquivC7 (X Y : Cols) : Prop := ∃ Q Qi : Cols, EquivData7 X Y Q Qi

instance (X Y Q Qi : Cols) : Decidable (EquivData7 X Y Q Qi) := by
  unfold EquivData7; infer_instance

theorem EquivData7.left_inv {X Y Q Qi : Cols} (h : EquivData7 X Y Q Qi) {v : ℕ} (hv : v < 16) :
    applyC Qi (applyC Q v) = v := by
  rw [← applyC_compC, h.2.2.1, applyC_idC hv]

theorem EquivData7.right_inv {X Y Q Qi : Cols} (h : EquivData7 X Y Q Qi) {v : ℕ} (hv : v < 16) :
    applyC Q (applyC Qi v) = v := by
  rw [← applyC_compC, h.2.2.2.1, applyC_idC hv]

theorem EquivData7.intertwine_x {X Y Q Qi : Cols} (h : EquivData7 X Y Q Qi) (v : ℕ) :
    applyC X (applyC Q v) = applyC Q (applyC modelX7 v) := by
  rw [← applyC_compC, ← applyC_compC, h.2.2.2.2.1]

theorem EquivData7.intertwine_y {X Y Q Qi : Cols} (h : EquivData7 X Y Q Qi) (v : ℕ) :
    applyC Y (applyC Q v) = applyC Q (applyC modelY7 v) := by
  rw [← applyC_compC, ← applyC_compC, h.2.2.2.2.2]

@[expose] def ModClass7 : Prop :=
  ∀ X Y : Cols, (∀ i, X.col i < 16) → (∀ i, Y.col i < 16) → RelC7 X Y →
    EquivC7 X Y ∨ EquivC7 X (evalC X Y twistWord7)


end CFSG.CGT.T75M23
