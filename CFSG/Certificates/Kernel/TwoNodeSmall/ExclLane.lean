module

public import CFSG.Certificates.Kernel.TwoNodeSmall.LaneSound
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.TwoNodeSmall.LaneSound

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK

@[expose] noncomputable def packR (p D : Nat) (r : Refl) : Nat × Nat := (pkP p D r.h, pkrP p D r.f)


@[expose] def frameRefl (lift : Bool) (p N : Nat) : List Refl :=
  (List.range (N - 1)).map fun k =>
    ⟨extOf lift (cartanRowP p N k) (if k = 0 then 1 else 0), unitP (dimOf lift N) k⟩

theorem frameK_eq (lift : Bool) (p N : Nat) :
    frameK lift p N = (frameRefl lift p N).map (packR p (dimOf lift N)) := by
  rw [frameRefl, List.map_map]
  rfl

theorem length_frameRefl (lift : Bool) (p N : Nat) : (frameRefl lift p N).length = N - 1 := by
  simp [frameRefl]

theorem getD_append_single {α : Type} (l : List α) (x d : α) (n : Nat) (hl : l.length = n) :
    (l ++ [x]).getD n d = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl, Nat.sub_self]
  rfl

@[expose] def vvOf (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (fr : Vec) : Vec :=
  extOf lift ((List.range (N - 1)).map fun k =>
    if inJ N s k then (if k - s = o.1 then o.2.2 else 0)
    else if (outsOf N s).head? = some k then fr.getD 0 0 else fr.getD 1 0) 0

@[expose] def ptOf (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (c fr : Vec) : Pt :=
  { p := p, D := dimOf lift N, nFrame := N - 1,
    gens := frameRefl lift p N ++ [⟨vvOf lift p N s o fr, extOf lift c 0⟩],
    x := extOf lift ((List.range (N - 1)).map (· + 1)) 0, bound := posBound p N }

theorem lastRefl_ptOf (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (c fr : Vec) :
    (ptOf lift p N s o c fr).lastRefl = ⟨vvOf lift p N s o fr, extOf lift c 0⟩ :=
  getD_append_single _ _ _ _ (length_frameRefl lift p N)

theorem gens_ptOf (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (c fr : Vec) :
    (ptOf lift p N s o c fr).gens = frameRefl lift p N ++ [(ptOf lift p N s o c fr).lastRefl] := by
  rw [lastRefl_ptOf]
  rfl


theorem frameK_append (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (c fr : Vec) :
    frameK lift p N ++ [packR p (dimOf lift N) (ptOf lift p N s o c fr).lastRefl] =
      (ptOf lift p N s o c fr).gens.map (packR p (ptOf lift p N s o c fr).D) := by
  rw [gens_ptOf, frameK_eq, List.map_append, List.map_cons, List.map_nil]
  rfl

theorem mem_allVecsP_two {p : Nat} {fr : Vec} (h : fr ∈ allVecsP p 2) :
    ∃ a b, fr = [a, b] ∧ a < p ∧ b < p := by
  simp only [allVecsP, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap,
    List.mem_map, List.mem_range] at h
  obtain ⟨v, ⟨b, hb, rfl⟩, a, ha, rfl⟩ := h
  exact ⟨a, b, rfl, ha, hb⟩

theorem rv_congr (D : Nat) {x y : Nat → Nat} (h : ∀ i < D, x i = y i) : rv D x = rv D y := by
  unfold rv
  exact enc_map_congr (fun i hi => h i (List.mem_range.mp (List.mem_reverse.mp hi)))

theorem rv_add (D : Nat) (x y : Nat → Nat) : rv D (fun i => x i + y i) = rv D x + rv D y := by
  unfold rv
  have h := enc_map_add ((List.range D).reverse) x y 1
  simp only [Nat.one_mul] at h
  exact h

theorem rv_eq_zero (D : Nat) (x : Nat → Nat) (hx : ∀ j < D, x j = 0) : rv D x = 0 := by
  induction D with
  | zero => rfl
  | succ D ih =>
    rw [rv_succ_last, ih (fun j hj => hx j (by omega)), hx D (by omega)]

theorem rv_unit (D o a : Nat) (ho : o < D) :
    rv D (fun i => if i = o then a else 0) = a * 65536 ^ (D - 1 - o) := by
  induction D with
  | zero => omega
  | succ D ih =>
    rw [rv_succ_last]
    rcases Nat.lt_or_ge o D with h | h
    · rw [ih h, if_neg (by omega)]
      have e : D + 1 - 1 - o = (D - 1 - o) + 1 := by omega
      rw [e, pow_succ]
      ring
    · have hoD : o = D := by omega
      subst hoD
      rw [rv_eq_zero o _ (fun j hj => if_neg (by omega)), if_pos rfl]
      simp

theorem rv_two (D o0 o1 a b : Nat) (h0 : o0 < D) (h1 : o1 < D) (x y : Nat → Nat)
    (h : ∀ i < D, y i = x i + (if i = o0 then a else 0) + (if i = o1 then b else 0)) :
    rv D y = rv D x + a * laneR D o0 + b * laneR D o1 := by
  rw [rv_congr D h, rv_add, rv_add, rv_unit D o0 a h0, rv_unit D o1 b h1, laneR, laneR, pow_mul,
    pow_mul]
  rfl

theorem outsOf_eq {p N s : Nat} (hpN : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7)) (hs : s < 3) :
    ∃ o0 o1, outsOf N s = [o0, o1] ∧ o0 ≠ o1 := by
  rcases hpN with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> interval_cases s
  · exact ⟨2, 3, by decide, by decide⟩
  · exact ⟨0, 3, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide⟩
  · exact ⟨4, 5, by decide, by decide⟩
  · exact ⟨0, 5, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide⟩

theorem mem_outsOf (N s i : Nat) : i ∈ outsOf N s ↔ i < N - 1 ∧ inJ N s i = false := by
  simp [outsOf, List.mem_filter]

theorem getD_extOf {N : Nat} (lift : Bool) (g : Nat → Nat) (i : Nat) (hi : i < dimOf lift N) :
    (extOf lift ((List.range (N - 1)).map g) 0).getD i 0 = if i < N - 1 then g i else 0 := by
  have hL : ((List.range (N - 1)).map g).length = N - 1 := by simp
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    have e : ((List.range (N - 1)).map g)[i]? = some (g i) := by
      rw [List.getElem?_map, List.getElem?_range h]
      rfl
    cases lift with
    | false => simp only [extOf, Bool.false_eq_true, if_false, e, Option.getD_some]
    | true => simp only [extOf, if_true, List.getElem?_append_left (hL ▸ h), e, Option.getD_some]
  · rename_i h
    cases lift with
    | false =>
      simp only [dimOf, Bool.false_eq_true, if_false] at hi
      omega
    | true =>
      simp only [dimOf, if_true] at hi
      simp only [extOf, if_true]
      rw [List.getElem?_append_right (by omega), hL]
      have e : i - (N - 1) = 0 := by omega
      rw [e]
      rfl

theorem vbK_add {lift : Bool} {p N s oi : Nat} (hpN : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7))
    (hs : s < 3) (a b : Nat) (ha : a < p) (hb : b < p) :
    vbK lift p N s oi + a * laneR (dimOf lift N) ((outsOf N s).getD 0 0) +
        b * laneR (dimOf lift N) ((outsOf N s).getD 1 0) =
      pkrP p (dimOf lift N) (vvOf lift p N s (optOf p N oi) [a, b]) := by
  simp only [vvOf, List.getD_cons_zero, List.getD_cons_succ]
  obtain ⟨o0, o1, ho, hne⟩ := outsOf_eq hpN hs
  have hm0 := (mem_outsOf N s o0).mp (by rw [ho]; simp)
  have hm1 := (mem_outsOf N s o1).mp (by rw [ho]; simp)
  have hND : N - 1 ≤ dimOf lift N := by cases lift <;> simp [dimOf]
  simp only [vbK, ho, pkrP_rv, List.getD_cons_zero, List.getD_cons_succ, List.head?_cons]
  symm
  refine rv_two _ o0 o1 a b (by omega) (by omega) _ _ (fun i hi => ?_)
  simp only [lnp]
  rw [getD_extOf lift _ i hi, getD_extOf lift _ i hi]
  split
  · rename_i hiN
    cases hJ : inJ N s i with
    | true =>
      have h0 : i ≠ o0 := by
        rintro rfl
        simp [hJ] at hm0
      have h1 : i ≠ o1 := by
        rintro rfl
        simp [hJ] at hm1
      simp [h0, h1]
    | false =>
      have hio : i ∈ outsOf N s := (mem_outsOf N s i).mpr ⟨hiN, hJ⟩
      rw [ho] at hio
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hio
      rcases hio with rfl | rfl
      · simp [hne, Nat.mod_eq_of_lt ha]
      · simp [hne, Ne.symm hne, Nat.mod_eq_of_lt hb]
  · rename_i hiN
    have h0 : i ≠ o0 := by omega
    have h1 : i ≠ o1 := by omega
    simp [h0, h1]

theorem ptsK_eq {lift : Bool} {p N s oi : Nat} (hpN : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7))
    (hs : s < 3) (cs : List Vec) :
    ptsK lift p N s oi cs = cs.flatMap fun c => (allVecsP p 2).map fun fr =>
      packR p (dimOf lift N) (ptOf lift p N s (optOf p N oi) c fr).lastRefl := by
  unfold ptsK
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, ih]
    congr 1
    apply List.map_congr_left
    intro fr hfr
    obtain ⟨a, b, rfl, ha, hb⟩ := mem_allVecsP_two hfr
    rw [lastRefl_ptOf]
    refine Prod.ext rfl ?_
    exact vbK_add hpN hs a b ha hb

end CFSG.TwoNodeSmall.LaneSound

end
