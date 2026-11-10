module

public import CFSG.CGT.T75JM.N6Cols
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.CGT.T75JM

@[expose] def modelX : Cols := ⟨1, 11, 12, 8⟩

@[expose] def modelY : Cols := ⟨10, 4, 5, 9⟩

@[expose] def evalC (X Y : Cols) : List ℕ → Cols
  | [] => idC
  | l :: w => compC (if l = 0 then X else Y) (evalC X Y w)

@[expose] def RelC (X Y : Cols) : Prop :=
  compC X X = idC ∧ X ≠ idC ∧ powC Y 4 = idC ∧ powC (compC X Y) 5 = idC ∧
    powC (compC X (compC Y Y)) 5 = idC

instance (X Y : Cols) : Decidable (RelC X Y) := by unfold RelC; infer_instance

@[expose] def twistWord : List ℕ := [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0]

@[expose] def EquivData (X Y Q Qi : Cols) : Prop :=
  (∀ i, Q.col i < 16) ∧ (∀ i, Qi.col i < 16) ∧ compC Qi Q = idC ∧ compC Q Qi = idC ∧
    compC X Q = compC Q modelX ∧ compC Y Q = compC Q modelY

@[expose] def EquivC (X Y : Cols) : Prop := ∃ Q Qi : Cols, EquivData X Y Q Qi

instance (X Y Q Qi : Cols) : Decidable (EquivData X Y Q Qi) := by
  unfold EquivData; infer_instance

theorem EquivData.left_inv {X Y Q Qi : Cols} (h : EquivData X Y Q Qi) {v : ℕ} (hv : v < 16) :
    applyC Qi (applyC Q v) = v := by
  rw [← applyC_compC, h.2.2.1, applyC_idC hv]

theorem EquivData.right_inv {X Y Q Qi : Cols} (h : EquivData X Y Q Qi) {v : ℕ} (hv : v < 16) :
    applyC Q (applyC Qi v) = v := by
  rw [← applyC_compC, h.2.2.2.1, applyC_idC hv]

theorem EquivData.intertwine_x {X Y Q Qi : Cols} (h : EquivData X Y Q Qi) (v : ℕ) :
    applyC X (applyC Q v) = applyC Q (applyC modelX v) := by
  rw [← applyC_compC, ← applyC_compC, h.2.2.2.2.1]

theorem EquivData.intertwine_y {X Y Q Qi : Cols} (h : EquivData X Y Q Qi) (v : ℕ) :
    applyC Y (applyC Q v) = applyC Q (applyC modelY v) := by
  rw [← applyC_compC, ← applyC_compC, h.2.2.2.2.2]

@[expose] def ModClass : Prop :=
  ∀ X Y : Cols, (∀ i, X.col i < 16) → (∀ i, Y.col i < 16) → RelC X Y →
    EquivC X Y ∨ EquivC X (evalC X Y twistWord)

@[expose] def packC (c : Cols) : ℕ := c.c0 + 16 * c.c1 + 256 * c.c2 + 4096 * c.c3

@[expose] def unpackC (m : ℕ) : Cols := ⟨m % 16, m / 16 % 16, m / 256 % 16, m / 4096 % 16⟩


theorem packC_lt {c : Cols} (hc : ∀ i, c.col i < 16) : packC c < 65536 := by
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2; have h3 := hc 3
  simp only [Cols.col] at h0 h1 h2 h3
  unfold packC; omega

theorem unpackC_packC {c : Cols} (hc : ∀ i, c.col i < 16) : unpackC (packC c) = c := by
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2; have h3 := hc 3
  simp only [Cols.col] at h0 h1 h2 h3
  obtain ⟨a, b, c', d⟩ := c
  simp only [unpackC, packC, Cols.mk.injEq] at h0 h1 h2 h3 ⊢
  omega


end CFSG.CGT.T75JM
