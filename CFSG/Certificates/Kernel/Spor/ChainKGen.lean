module

public import CFSG.Certificates.Kernel.Spor.ChainKProof
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KS.CH

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.ONSchreier.Native

theorem foldl_setK_congr {n : Nat} {t u : Array Nat} (h : ∀ i < n, t[i]! = u[i]!) :
    ∀ (l : List Nat) (p : Array Nat), (∀ i ∈ l, i < n) →
      l.foldl (fun p i => p.set! t[i]! i) p = l.foldl (fun p i => p.set! u[i]! i) p
  | [], _, _ => rfl
  | a :: l, p, hl => by
    simp only [List.foldl_cons]
    rw [h a (hl a (by simp))]
    exact foldl_setK_congr h l _ fun i hi => hl i (by simp [hi])

theorem pinvCand_eq_of_agree {n : Nat} {t u : Array Nat} (h : ∀ i < n, t[i]! = u[i]!) :
    pinvCand n t = pinvCand n u := by
  have key : ∀ v : Array Nat, pinvCand n v =
      (List.range' 0 n).foldl (fun p i => p.set! v[i]! i) (Array.replicate n 0) := fun v => by
    unfold pinvCand
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  rw [key, key]
  exact foldl_setK_congr h _ _ fun i hi => by simpa using (List.mem_range'_1.1 hi).2

theorem pinvs_get {n s : Nat} {S : Array (Array Nat)} {F FI : Nat → Nat → Nat}
    (hS : S.size = s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x) :
    ∀ j < s, ∀ x < n, ((pinvs n S)[j]!)[x]! = FI j x := by
  intro j hj x hx
  unfold pinvs
  rw [getElem!_pos _ j (by simp [hS]; exact hj), Array.getElem_map,
    ← getElem!_pos S j (by rw [hS]; exact hj),
    pinvCand_eq_of_agree (u := Array.ofFn (n := n) fun i => F j i.val) fun i hi => by
      rw [getD_ofFn (f := F j) hi]
      exact (hF j hj i hi).1]
  exact CFSG.KS.CB.pinvCand_get (T := F j) (U := FI j) (fun y hy => (hF j hj y hy).2.1)
    (fun y hy => (hF j hj y hy).2.2.2) hx

theorem trInvK_lt_nz {n m r : Nat} {PAR LAB : Nat → Nat} {INV : Nat → Nat → Nat}
    (hm : ∀ k < m, k ≠ 0 → PAR k < m ∧ LAB k < r) (hI : ∀ j < r, ∀ x < n, INV j x < n) :
    ∀ fuel k p, k < m → p < n → trInvK PAR LAB INV fuel k p < n
  | 0, _, _, _, hp => hp
  | f + 1, k, p, hk, hp => by
    change nIf(Nat.beq k 0, p, trInvK PAR LAB INV f (PAR k) (INV (LAB k) p)) < n
    rw [nIf_v]
    split
    · exact hp
    · rename_i h
      have hk0 : k ≠ 0 := fun e => h (by rw [e]; rfl)
      exact trInvK_lt_nz hm hI f _ _ (hm k hk hk0).1 (hI _ (hm k hk hk0).2 _ hp)

theorem trInvApp_eq_nz {n m r : Nat} {PTS POS PAR LAB : Nat → Nat} {INV : Nat → Nat → Nat}
    {invs : Array (Array Nat)} (hm : ∀ k < m, k ≠ 0 → PAR k < m ∧ LAB k < r)
    (hinv : ∀ j < r, ∀ x < n, invs[j]![x]! = INV j x ∧ INV j x < n) :
    ∀ (fuel k p : Nat), k < m → p < n →
      trInvApp invs ⟨Array.ofFn (n := m) fun k => PTS k.val, Array.ofFn (n := n) fun z => POS z.val,
        Array.ofFn (n := m) fun k => PAR k.val, Array.ofFn (n := m) fun k => LAB k.val⟩ fuel k p =
      trInvK PAR LAB INV fuel k p
  | 0, _, _, _, _ => rfl
  | fuel + 1, k, p, hk, hp => by
    unfold trInvApp
    by_cases h0 : k = 0
    · subst h0
      rfl
    · have hbk : (k == 0) = false := by simpa using h0
      simp only [hbk, Bool.false_eq_true, ↓reduceIte]
      have e1 : (Array.ofFn (n := m) fun k => PAR k.val)[k]! = PAR k := by
        rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
      have e2 : (Array.ofFn (n := m) fun k => LAB k.val)[k]! = LAB k := by
        rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
      have hmk := hm k hk h0
      rw [e1, e2, (hinv (LAB k) hmk.2 p hp).1,
        trInvApp_eq_nz hm hinv fuel (PAR k) (INV (LAB k) p) hmk.1 (hinv (LAB k) hmk.2 p hp).2]
      change _ = nIf(Nat.beq k (nat_lit 0), p, trInvK PAR LAB INV fuel (PAR k) (INV (LAB k) p))
      have hb0 : Nat.beq k (nat_lit 0) = false := by
        cases k with
        | zero => exact absurd rfl h0
        | succ k => rfl
      rw [hb0]


end CFSG.KS.CH

end
