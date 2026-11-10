module

public import Certificates.Data.Kernel.J4Q.VOrb
public import CFSG.Certificates.Kernel.J4Q.Rep
import CFSG.Certificates.Kernel.J4Q.VOrbBFS
import CFSG.Certificates.Kernel.J4Q.VOrbTree

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.Native CFSG.KC.LQT.Syl

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

@[expose] noncomputable def pchK (rm root : Nat) (chs : List (List Nat)) : List (List Nat) :=
  List.cons (List.cons root List.nil) (List.map (List.map fun e => Nat.land e rm) chs)

private theorem andB_true (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

private theorem vecLFrom_cons (x r : Nat) (t : List Nat) (k acc : Nat) :
    vecLFrom x (r :: t) k acc =
      vecLFrom x t (k + 1) (if Nat.land (Nat.shiftRight x k) 1 = 1 then acc ^^^ r else acc) := by
  change Bool.rec (motive := fun _ => Nat) (vecLFrom x t (k + 1) acc)
    (CFSG.KC.Loop.strictN (Nat.xor acc r) (vecLFrom x t (k + 1)))
    (Nat.beq (Nat.land (Nat.shiftRight x k) 1) 1) = _
  have hs : ∀ y, CFSG.KC.Loop.strictN y (vecLFrom x t (k + 1)) = vecLFrom x t (k + 1) y := by
    intro y
    cases y <;> rfl
  rw [hs]
  cases hb : Nat.beq (Nat.land (Nat.shiftRight x k) 1) 1 with
  | false => rw [ite_eq_right (Nat.ne_of_beq_eq_false hb)]
  | true =>
    rw [ite_eq_left (Nat.eq_of_beq_eq_true hb)]
    rfl

private theorem vecLFrom_range (x : Nat) (g : Nat → Nat) : ∀ n k,
    vecLFrom x ((List.range' k n).map g) k (xsum (fun j => ((x >>> j) &&& 1) * g j) k) =
      xsum (fun j => ((x >>> j) &&& 1) * g j) (k + n)
  | 0, k => by simp only [List.range'_zero, List.map_nil, Nat.add_zero]; rfl
  | n + 1, k => by
    rw [List.range'_succ, List.map_cons, vecLFrom_cons]
    have hstep : (if Nat.land (Nat.shiftRight x k) 1 = 1 then
        xsum (fun j => ((x >>> j) &&& 1) * g j) k ^^^ g k
        else xsum (fun j => ((x >>> j) &&& 1) * g j) k) =
        xsum (fun j => ((x >>> j) &&& 1) * g j) (k + 1) := by
      rw [xsum_succ]
      have h01 : (x >>> k) &&& 1 = 0 ∨ (x >>> k) &&& 1 = 1 := by
        rw [Nat.and_one_is_mod]
        omega
      change (if (x >>> k) &&& 1 = 1 then _ else _) = _
      rcases h01 with h | h <;> simp [h]
    rw [hstep, vecLFrom_range x g n (k + 1), Nat.add_right_comm, Nat.add_assoc]

private theorem rowsOfJ_eq (rm M : Nat) : rowsOfJ rm M = (List.range' 0 112).map (rowJ rm M) :=
  rfl

theorem vecLJ_rowsOfJ (rm x M : Nat) : vecLJ x (rowsOfJ rm M) = vecJ rm x M := by
  rw [vecJ_eq, rowsOfJ_eq]
  exact vecLFrom_range x (rowJ rm M) 112 0

private theorem getN_eq (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], i => by
    rw [List.getD_nil]
    rfl
  | _ :: _, 0 => rfl
  | m :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact getN_eq d l i

private theorem dropK_eq : ∀ (n : Nat) (l : List Nat), dropK n l = l.drop n
  | 0, l => rfl
  | n + 1, l => by
    change List.rec (motive := fun _ => List Nat) List.nil (fun _ t _ => t) (dropK n l) = _
    rw [dropK_eq n l, ← List.tail_drop]
    cases l.drop n <;> rfl

private theorem headK_drop (n : Nat) (l : List Nat) : headK (l.drop n) = l.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, ← List.head?_drop]
  cases l.drop n <;> rfl

private theorem vtGo_sound (rm : Nat) (Rs : List (List Nat)) (P : List Nat) :
    ∀ (ch : List Nat) (ci k : Nat), vtGo rm Rs ch (P.drop ci) ci k = true →
      ∀ j < ch.length, ∃ par < k + j, ∃ lab < Rs.length,
        vecLJ (P.getD par 0) (Rs.getD lab []) = Nat.land (ch.getD j 0) rm
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | e :: ch, ci, k, h, j, hj => by
    change andB (Nat.ble ci (Nat.shiftRight e 114)) (andB (Nat.blt (Nat.shiftRight e 114) k)
      (andB (Nat.blt (Nat.land (Nat.shiftRight e 112) 3) Rs.length)
        (andB (Nat.beq (vecLJ (headK (dropK (Nat.shiftRight e 114 - ci) (P.drop ci)))
          (Rs.getD (Nat.land (Nat.shiftRight e 112) 3) [])) (Nat.land e rm))
          (vtGo rm Rs ch (dropK (Nat.shiftRight e 114 - ci) (P.drop ci)) (Nat.shiftRight e 114)
            (k + 1))))) = true at h
    simp only [andB_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hd : dropK (Nat.shiftRight e 114 - ci) (P.drop ci) = P.drop (Nat.shiftRight e 114) := by
      rw [dropK_eq, List.drop_drop, Nat.add_sub_cancel' h1]
    rw [hd] at h4 h5
    cases j with
    | zero =>
      refine ⟨_, by omega, _, h3, ?_⟩
      rw [← headK_drop, h4]
      rfl
    | succ j =>
      obtain ⟨par, hpar, lab, hlab, he⟩ := vtGo_sound rm Rs P ch _ (k + 1) h5 j
        (by simpa using hj)
      exact ⟨par, by omega, lab, hlab, by rw [he]; rfl⟩

private theorem flatten_index {B : Nat} : ∀ {chs : List (List Nat)},
    (∀ i, i + 1 < chs.length → (chs.getD i []).length = B) →
    ∀ t < chs.flatten.length, ∃ i < chs.length, ∃ j < (chs.getD i []).length,
      t = B * i + j ∧ chs.flatten.getD t 0 = (chs.getD i []).getD j 0
  | [], _, t, ht => by simp at ht
  | c :: cs, hB, t, ht => by
    rw [List.flatten_cons, List.length_append] at ht
    by_cases htc : t < c.length
    · refine ⟨0, by simp, t, by simpa using htc, by simp, ?_⟩
      rw [List.flatten_cons, List.getD_append _ _ _ _ htc]
      rfl
    · have hcs : cs ≠ [] := by
        rintro rfl
        simp at ht
        omega
      have hcB : c.length = B := by
        have := hB 0 (by simpa using List.length_pos_of_ne_nil hcs)
        simpa using this
      obtain ⟨i, hi, j, hj, he, hg⟩ := flatten_index (chs := cs)
        (fun i hi => by simpa using hB (i + 1) (by simpa using hi)) (t - c.length) (by omega)
      refine ⟨i + 1, by simpa using hi, j, by simpa using hj, ?_, ?_⟩
      · rw [Nat.mul_succ]
        omega
      · rw [List.flatten_cons, List.getD_append_right _ _ _ _ (by omega)]
        simpa using hg


end CFSG.KC.J4Q

end
