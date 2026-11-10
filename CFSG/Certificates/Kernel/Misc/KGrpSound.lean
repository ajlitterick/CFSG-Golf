module

public import Certificates.Data.Kernel.Misc.KGrp
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.GH74.KGroups.ClassCount

public section

namespace CFSG.KC.Misc.KG

open Equiv CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.GH74.KGroups

variable {n : ℕ}

theorem beq_true_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem notB_iff {a : Bool} : notB a = true ↔ ¬ a = true := by
  cases a <;> simp [notB]

theorem impB_iff {a b : Bool} : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp [impB]

theorem allL_iff (L : List ℕ) (f : ℕ → Bool) : allL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => simp [allL]
  | cons x L ih =>
    change andB (f x) (allL L f) = true ↔ _
    rw [andB_iff, ih]
    simp

theorem anyL_iff (L : List ℕ) (f : ℕ → Bool) : anyL L f = true ↔ ∃ x ∈ L, f x = true := by
  induction L with
  | nil => simp [anyL]
  | cons x L ih =>
    change orB (f x) (anyL L f) = true ↔ _
    rw [orB_iff, ih]
    simp

theorem memL_iff (c : ℕ) (L : List ℕ) : memL c L = true ↔ c ∈ L := by
  rw [memL, anyL_iff]
  simp

theorem pcode_mul (hn : n ≤ 32) (a b : Perm (Fin n)) :
    P.mul n (pcode a) (pcode b) = pcode (a * b) := ((pcode_enc hn).enc_mul a b).symm

theorem pcode_one (hn : n ≤ 32) : P.one n = pcode (1 : Perm (Fin n)) := (pcode_enc hn).enc_one.symm

theorem pcode_inj (hn : n ≤ 32) {a b : Perm (Fin n)} : pcode a = pcode b ↔ a = b :=
  ⟨fun h => (pcode_enc hn).inj h, congrArg _⟩

theorem pcode_pow (hn : n ≤ 32) (g : Perm (Fin n)) (k : ℕ) : P.pow n (pcode g) k = pcode (g ^ k) := by
  induction k with
  | zero => exact (pcode_one hn).trans (by rw [pow_zero])
  | succ k ih =>
    change P.mul n (P.pow n (pcode g) k) (pcode g) = _
    rw [ih, pcode_mul hn, pow_succ]

theorem beq_iff (hn : n ≤ 32) (a b : Perm (Fin n)) : Nat.beq (pcode a) (pcode b) = true ↔ a = b := by
  rw [beq_true_iff, pcode_inj hn]

theorem isOne_iff (hn : n ≤ 32) (g : Perm (Fin n)) : isOne n (pcode g) = true ↔ g = 1 := by
  rw [isOne, pcode_one hn, beq_iff hn]

theorem comm_iff (hn : n ≤ 32) (a b : Perm (Fin n)) :
    P.comm n (pcode a) (pcode b) = true ↔ a * b = b * a := by
  rw [P.comm, pcode_mul hn, pcode_mul hn, beq_iff hn]

theorem cubeOne_iff (hn : n ≤ 32) (g : Perm (Fin n)) : cubeOne n (pcode g) = true ↔ g ^ 3 = 1 := by
  rw [cubeOne, pcode_pow hn, isOne_iff hn]


theorem ordGo_iff (hn : n ≤ 32) (g : Perm (Fin n)) (k j : ℕ) :
    ordGo n (pcode g) k (pcode (g ^ j)) = true ↔ (∀ i < k, g ^ (j + i) ≠ 1) ∧ g ^ (j + k) = 1 := by
  induction k generalizing j with
  | zero =>
    change isOne n (pcode (g ^ j)) = true ↔ _
    rw [isOne_iff hn]
    simp
  | succ k ih =>
    change letB (pcode (g ^ j)) (fun a => andB (notB (isOne n a))
      (ordGo n (pcode g) k (P.mul n a (pcode g)))) = true ↔ _
    rw [letB_eq, andB_iff, notB_iff, isOne_iff hn, pcode_mul hn, ← pow_succ, ih (j + 1)]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun i hi => ?_, by rwa [show j + (k + 1) = j + 1 + k by omega]⟩
      rcases i with _ | i
      · simpa using h0
      · have := h1 i (by omega)
        rwa [show j + 1 + i = j + (i + 1) by omega] at this
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa using h1 0 (by omega), fun i hi => ?_, by
        rwa [show j + 1 + k = j + (k + 1) by omega]⟩
      have := h1 (i + 1) (by omega)
      rwa [show j + (i + 1) = j + 1 + i by omega] at this

theorem ordK_iff (hn : n ≤ 32) (g : Perm (Fin n)) {m : ℕ} (hm : 0 < m) :
    ordK n (pcode g) m = true ↔ orderOf g = m := by
  have h := ordGo_iff hn g (m - 1) 1
  rw [pow_one] at h
  rw [ordK, Nat.sub_eq, h, orderOf_eq_iff hm, show 1 + (m - 1) = m by omega]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun i hi hi0 => ?_⟩
    have := h1 (i - 1) (by omega)
    rwa [show 1 + (i - 1) = i by omega] at this
  · rintro ⟨h2, h1⟩
    exact ⟨fun i hi => h1 (1 + i) (by omega) (by omega), h2⟩


variable {H : Subgroup (Perm (Fin n))} {N : ℕ} {E : ℕ → ℕ}

theorem exact_forall (hE : ExactList pcode H N E) (F : ℕ → Bool) (h : ∀ k < N, F (E k) = true) :
    ∀ g ∈ H, F (pcode g) = true := by
  intro g hg
  obtain ⟨k, hk, he⟩ := hE.2.1 g hg
  rw [he]
  exact h k hk


theorem cntN_eq_card (N : ℕ) (f : ℕ → Bool) :
    cntN N f = ((Finset.range N).filter fun k => f k = true).card := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change cntN N f + Bool.rec (motive := fun _ => ℕ) 0 1 (f N) = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    cases hf : f N
    · simp
    · rw [ite_eq_left rfl, Finset.card_insert_of_notMem (by simp)]


theorem mem_CL (hn : n ≤ 32) (hE : ExactList pcode H N E) {r : Perm (Fin n)} {R : ℕ}
    (hr : pcode r = R) {CL : List ℕ} (hc : ∀ k < N, inCAt n E R CL k = true) :
    ∀ g ∈ H, g * r = r * g → pcode g ∈ CL := by
  intro g hg hgr
  have := exact_forall hE (fun g => impB (P.comm n g R) (memL g CL))
    (fun k hk => by have := hc k hk; rwa [inCAt, letB_eq] at this) g hg
  rw [impB_iff, ← hr, comm_iff hn, memL_iff] at this
  exact this hgr


end CFSG.KC.Misc.KG

end
