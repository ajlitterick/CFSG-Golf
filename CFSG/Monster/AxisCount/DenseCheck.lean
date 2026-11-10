module

public import CFSG.Monster.AxisCount.DenseNative
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public import Certificates.Certificate6007
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

namespace CFSG.Monster.AxisCount.Native

open CFSG.Monster.B.Rep4371.Native

theorem tabCheck_eq : tabCheck () = true :=
  Certificates.certificate6007.1

theorem tabCheck_parts :
    pairTab.size = 276 ∧
    (∀ tp, tp < 276 → pairTab[tp]!.1 < pairTab[tp]!.2 ∧ pairTab[tp]!.2 < 24 ∧
      pairIdx pairTab[tp]!.1 pairTab[tp]!.2 = tp) ∧
    (∀ i j, i < 24 → j < 24 → aIdx i j < 300 ∧ aPos (aIdx i j) = (min i j, max i j)) ∧
    octTab.size = 759 ∧
    (∀ o, o < 759 → octTab[o]! < 4096 ∧ popcN 24 (wordN octTab[o]!) = 8) ∧
    evenTab.size = 64 ∧
    (∀ q, q < 64 → evenTab[q]! < 128 ∧ popcN 8 evenTab[q]! % 2 = 0) := by
  have h := tabCheck_eq
  simp only [tabCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨by simpa using h1, fun tp htp => ?_, fun i j hi hj => ?_, by simpa using h4,
    fun o ho => ?_, by simpa using h6, fun q hq => ?_⟩
  · have := List.all_eq_true.1 h2 tp (List.mem_range.2 htp)
    simpa [and_assoc] using this
  · have := List.all_eq_true.1 (List.all_eq_true.1 h3 i (List.mem_range.2 hi)) j
      (List.mem_range.2 hj)
    simpa [and_assoc] using this
  · have := List.all_eq_true.1 h5 o (List.mem_range.2 ho)
    simpa [and_assoc] using this
  · have := List.all_eq_true.1 h7 q (List.mem_range.2 hq)
    simpa [and_assoc] using this


theorem pairTab_spec (tp : Nat) (h : tp < 276) :
    pairTab[tp]!.1 < pairTab[tp]!.2 ∧ pairTab[tp]!.2 < 24 ∧
      pairIdx pairTab[tp]!.1 pairTab[tp]!.2 = tp := tabCheck_parts.2.1 tp h

theorem aIdx_spec (i j : Nat) (hi : i < 24) (hj : j < 24) :
    aIdx i j < 300 ∧ aPos (aIdx i j) = (min i j, max i j) := tabCheck_parts.2.2.1 i j hi hj


theorem octTab_spec (o : Nat) (h : o < 759) :
    octTab[o]! < 4096 ∧ popcN 24 (wordN octTab[o]!) = 8 := tabCheck_parts.2.2.2.2.1 o h

theorem evenTab_size :
    evenTab.size = 64 := tabCheck_parts.2.2.2.2.2.1

theorem evenTab_spec (q : Nat) (h : q < 64) :
    evenTab[q]! < 128 ∧ popcN 8 evenTab[q]! % 2 = 0 := tabCheck_parts.2.2.2.2.2.2 q h

theorem octCheck_parts (o : Nat) (ho : o < 759) :
    (∀ m, m < 256 →
      spreadG (wordN octTab[o]!) m &&& wordN octTab[o]! = spreadG (wordN octTab[o]!) m ∧
      popcN 24 (spreadG (wordN octTab[o]!) m) = popcN 8 m ∧
      spreadG (wordN octTab[o]!) (m ^^^ 255) =
        spreadG (wordN octTab[o]!) m ^^^ wordN octTab[o]!) ∧
    (∀ m m', m < 256 → m' < 256 →
      spreadG (wordN octTab[o]!) (m &&& m') =
        spreadG (wordN octTab[o]!) m &&& spreadG (wordN octTab[o]!) m' ∧
      (m = m' ∨ spreadG (wordN octTab[o]!) m ≠ spreadG (wordN octTab[o]!) m')) :=
  Certificates.certificate6007.2.1 o ho


theorem ctx_key_spec (p : Nat) (hp : p < 98280) :
    (mkCtx ()).keys[p]!.1 < 4096 ∧ (mkCtx ()).keys[p]!.2 < 4096 ∧
      (mkCtx ()).find (mkCtx ()).keys[p]!.1 (mkCtx ()).keys[p]!.2 = p :=
  Certificates.certificate6007.2.2.2 p hp


theorem latA_aIdx
    (G D : Array Int) (i j : Nat) (hi : i < 24) (hj : j < 24) :
    (latA G D).getD (aIdx i j) 0 =
      ∑ k ∈ Finset.range 24, ∑ l ∈ Finset.range 24,
        G.getD (k * 24 + i) 0 * D.getD (aIdx k l) 0 * G.getD (l * 24 + j) 0 := by
  obtain ⟨h300, hpos⟩ := aIdx_spec i j hi hj
  unfold latA
  simp only []
  rw [getD_ofFn _ _ h300]
  simp only [getElem!_eq_getD', hpos]
  rcases le_total i j with hij | hji
  · rw [min_eq_left hij, max_eq_right hij]
    exact latA_aIdx_aux G D i j hi hj
  · rw [min_eq_right hji, max_eq_left hji, latA_aIdx_aux G D j i hj hi, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [aIdx_comm l k]
    ring

end CFSG.Monster.AxisCount.Native
