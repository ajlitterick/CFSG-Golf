module

public import Certificates.Data.CFSGNative.MonsterB.DyadicElim
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native


@[expose] def bz (M : ℕ) (v : ByteArray) (k : ℕ) : ZMod M := ((v.get! k).toNat : ZMod M)


theorem allLt_iff {n : ℕ} {p : ℕ → Bool} : allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i i.2

theorem allLt_spec {n : ℕ} {p : ℕ → Bool} (h : allLt n p = true) {i : ℕ} (hi : i < n) :
    p i = true :=
  allLt_iff.1 h i hi

theorem parLt_spec {n chunks : ℕ} {p : ℕ → Bool} (hc : 0 < chunks)
    (h : parLt n chunks p = true) : ∀ i < n, p i = true := by
  intro i hi
  unfold parLt at h
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply] at h
  set sz := n / chunks + 1 with hsz
  have hsz0 : 0 < sz := Nat.succ_pos _
  have hj : i / sz < chunks := by
    rw [Nat.div_lt_iff_lt_mul hsz0]
    have h1 := Nat.div_add_mod n chunks
    have h2 := Nat.mod_lt n hc
    have : chunks * sz = chunks * (n / chunks) + chunks := by rw [hsz]; ring
    rw [this]
    generalize chunks * (n / chunks) = A at h1 ⊢
    omega
  have hstep := h (i / sz) hj
  change allLt sz (fun k => !(decide (i / sz * sz + k < n)) || p (i / sz * sz + k)) = true
    at hstep
  have := allLt_spec hstep (Nat.mod_lt i hsz0)
  have e : i / sz * sz + i % sz = i := by
    rw [mul_comm]
    exact Nat.div_add_mod i sz
  rw [e] at this
  simpa [hi] using this


@[expose] def sing (n : ℕ) (c : ℤ) (i : ℕ) : Fin n → ℤ := fun l => if (l : ℕ) = i then c else 0


end CFSG.Monster.B.Dyadic
