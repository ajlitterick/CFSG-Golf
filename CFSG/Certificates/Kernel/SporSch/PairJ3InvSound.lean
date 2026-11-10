module

public import Certificates.Data.Kernel.SporSch.PairJ3Faith
public import CFSG.Sporadic.Schreier.PairF2Sep

public section

namespace CFSG.KS.SporSch.PF2

open CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.SmallF2.Native CFSG.KLie.CT CFSG.KC.M1F2

@[expose] noncomputable def unpackP (d M : Nat) : Array Nat :=
  Array.ofFn (n := d) fun i => rowF d M i.val

@[expose] def pivA (d c : Nat) (a : Array Nat) : Nat :=
  (List.range' c (d - c)).foldl (fun piv i => if (piv == d && a[i]!.testBit c) = true then i else piv) d

@[expose] def elimStepA (c ap rp : Nat) (s : Array Nat × Array Nat) (i : Nat) :
    Array Nat × Array Nat :=
  if (i != c && s.1[i]!.testBit c) = true then
    (s.1.set! i (s.1[i]! ^^^ ap), s.2.set! i (s.2[i]! ^^^ rp)) else (s.1, s.2)

@[expose] def elimA (d c ap rp : Nat) (s : Array Nat × Array Nat) : Array Nat × Array Nat :=
  (List.range' 0 d).foldl (elimStepA c ap rp) s

@[expose] def colA (d c : Nat) (s : Array Nat × Array Nat) : Array Nat × Array Nat :=
  if pivA d c s.1 < d then
    elimA d c s.1[pivA d c s.1]! s.2[pivA d c s.1]!
      ((s.1.set! (pivA d c s.1) s.1[c]!).set! c s.1[pivA d c s.1]!,
        (s.2.set! (pivA d c s.1) s.2[c]!).set! c s.2[pivA d c s.1]!)
  else (s.1, s.2)

theorem ite_yield {β : Type} {C : Prop} [Decidable C] (x y : β) :
    (if C then (pure (ForInStep.yield x) : Id (ForInStep β)) else pure (ForInStep.yield y)) =
      pure (ForInStep.yield (if C then x else y)) := by
  split <;> rfl

theorem invRowsF2_fold (d : Nat) (M : Array Nat) :
    invRowsF2 d M = ((List.range' 0 d).foldl (fun s c => colA d c s) (M, idRows d)).2 := by
  unfold invRowsF2 colA pivA elimA
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, ite_yield,
    List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

@[expose] def pivP (d c : Nat) (L : List (Nat × Nat)) : Nat :=
  (List.range' c (d - c)).foldl
    (fun piv i => if (piv == d && (L.getD i (0, 0)).1.testBit c) = true then i else piv) d

@[expose] def elimF (c ap rp j : Nat) (p : Nat × Nat) : Nat × Nat :=
  if (j != c && p.1.testBit c) = true then (p.1 ^^^ ap, p.2 ^^^ rp) else p

@[expose] def elimStepP (c ap rp : Nat) (L : List (Nat × Nat)) (i : Nat) : List (Nat × Nat) :=
  L.set i (elimF c ap rp i (L.getD i (0, 0)))

@[expose] def elimP (d c ap rp : Nat) (L : List (Nat × Nat)) : List (Nat × Nat) :=
  (List.range' 0 d).foldl (elimStepP c ap rp) L

@[expose] def colP (d c : Nat) (L : List (Nat × Nat)) : List (Nat × Nat) :=
  if pivP d c L < d then
    elimP d c (L.getD (pivP d c L) (0, 0)).1 (L.getD (pivP d c L) (0, 0)).2
      ((L.set (pivP d c L) (L.getD c (0, 0))).set c (L.getD (pivP d c L) (0, 0)))
  else L

theorem arr_get (a : Array Nat) (i : Nat) : a[i]! = a.toList.getD i 0 := by
  rcases a with ⟨l⟩
  simp only [getElem!_def, List.getD_eq_getElem?_getD, List.getElem?_toArray]
  cases l[i]? <;> rfl

theorem zip_getD (l1 l2 : List Nat) (h : l1.length = l2.length) (i : Nat) :
    (List.zip l1 l2).getD i (0, 0) = (l1.getD i 0, l2.getD i 0) := by
  induction l1 generalizing l2 i with
  | nil => cases l2 <;> simp_all
  | cons x l1 ih =>
    cases l2 with
    | nil => simp at h
    | cons y l2 =>
      cases i with
      | zero => rfl
      | succ i => simpa using ih l2 (by simpa using h) i


@[expose] def zA (s : Array Nat × Array Nat) : List (Nat × Nat) := List.zip s.1.toList s.2.toList


theorem bit_eq (X i : Nat) : bit X i = X.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff, Nat.beq_eq,
    decide_eq_true_iff]

theorem strictL_eq (y : Nat) (k : Nat → List (Nat × Nat)) : strictL y k = k y := by
  cases y <;> rfl

theorem getPK_eq (L : List (Nat × Nat)) (i : Nat) : getPK L i = L.getD i (0, 0) := by
  induction L generalizing i with
  | nil => rfl
  | cons x L ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem setPK_eq (L : List (Nat × Nat)) (i : Nat) (p : Nat × Nat) : setPK L i p = L.set i p := by
  induction L generalizing i with
  | nil => rfl
  | cons x L ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (x :: ·) (ih i)

theorem cond_eq (i c a : Nat) :
    Bool.rec (motive := fun _ => Bool) false (bit a c)
      (Bool.rec (motive := fun _ => Bool) true false (Nat.beq i c)) = (i != c && a.testBit c) := by
  rw [bit_eq]
  cases h : Nat.beq i c
  · have : i ≠ c := fun e => by simp [e] at h
    simp [this]
  · have : i = c := Nat.eq_of_beq_eq_true h
    simp [this]

theorem elimGo_eq (c ap rp : Nat) (L : List (Nat × Nat)) (i : Nat) :
    elimGo c ap rp L i = L.mapIdx (fun j p => elimF c ap rp (i + j) p) := by
  induction L generalizing i with
  | nil => rfl
  | cons x L ih =>
    obtain ⟨a, r⟩ := x
    rw [List.mapIdx_cons]
    change Bool.rec (motive := fun _ => List (Nat × Nat)) ((a, r) :: elimGo c ap rp L (i + 1))
        ((Nat.xor a ap, Nat.xor r rp) :: elimGo c ap rp L (i + 1))
        (Bool.rec (motive := fun _ => Bool) false (bit a c)
          (Bool.rec (motive := fun _ => Bool) true false (Nat.beq i c))) = _
    rw [cond_eq, ih]
    have e : (fun j p => elimF c ap rp (i + (j + 1)) p) = fun j p => elimF c ap rp (i + 1 + j) p := by
      funext j p
      rw [Nat.add_comm j 1, Nat.add_assoc]
    rw [e]
    unfold elimF
    cases (i != c && a.testBit c) <;> rfl

theorem elimP_eq (c ap rp : Nat) (L : List (Nat × Nat)) :
    elimP L.length c ap rp L = L.mapIdx (fun j p => elimF c ap rp j p) := by
  have key : ∀ k, k ≤ L.length → (List.range' 0 k).foldl (elimStepP c ap rp) L =
      L.mapIdx (fun j p => if j < k then elimF c ap rp j p else p) := by
    intro k
    induction k with
    | zero =>
      intro _
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp
    | succ k ih =>
      intro hk
      rw [List.range'_concat, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      simp only [Nat.zero_add, Nat.one_mul]
      have hkL : k < L.length := by omega
      have hg : (L.mapIdx (fun j p => if j < k then elimF c ap rp j p else p)).getD k (0, 0) =
          L[k] := by
        rw [List.getD_eq_getElem _ _ (by simpa using hkL), List.getElem_mapIdx]
        simp
      unfold elimStepP
      rw [hg]
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp only [List.getElem_set, List.getElem_mapIdx]
      by_cases hj : k = j
      · subst hj
        simp
      · simp only [hj, ite_eq_right, not_false_eq_true]
        by_cases h3 : j < k
        · simp [h3, show j < k + 1 by omega]
        · simp [h3, show ¬ j < k + 1 by omega]
  unfold elimP
  rw [key L.length le_rfl]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_mapIdx]
  rw [ite_eq_left (by simpa using h1)]

theorem elimK_eq (c ap rp : Nat) (L : List (Nat × Nat)) :
    elimK c ap rp L = elimP L.length c ap rp L := by
  rw [elimP_eq, elimK, elimGo_eq]
  simp only [Nat.zero_add]

@[expose] def stepQ (d c : Nat) (L : List (Nat × Nat)) (piv j : Nat) : Nat :=
  if (piv == d && (decide (c ≤ j) && (L.getD j (0, 0)).1.testBit c)) = true then j else piv

theorem stepQ_keep (d c : Nat) (L : List (Nat × Nat)) (l : List Nat) (piv : Nat) (h : piv ≠ d) :
    l.foldl (stepQ d c L) piv = piv := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons]
    have : stepQ d c L piv j = piv := by
      unfold stepQ
      simp [h]
    rw [this, ih]

theorem pivGo_eq (d c : Nat) (L : List (Nat × Nat)) (hL : L.length ≤ d) :
    ∀ n i, i + n = L.length → pivGo d c (L.drop i) i = (List.range' i n).foldl (stepQ d c L) d := by
  intro n
  induction n with
  | zero =>
    intro i hi
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ n ih =>
    intro i hi
    have hiL : i < L.length := by omega
    rw [List.drop_eq_getElem_cons hiL, List.range'_succ, List.foldl_cons]
    rcases hx : L[i] with ⟨a, r⟩
    have hg : L.getD i (0, 0) = (a, r) := by rw [List.getD_eq_getElem _ _ hiL, hx]
    change Bool.rec (motive := fun _ => Nat) (pivGo d c (L.drop (i + 1)) (i + 1)) i
        (Bool.rec (motive := fun _ => Bool) false (bit a c) (Nat.ble c i)) = _
    rw [ih (i + 1) (by omega), bit_eq]
    have hs : stepQ d c L d i = if (decide (c ≤ i) && a.testBit c) = true then i else d := by
      unfold stepQ
      rw [hg]
      simp
    rw [hs]
    by_cases hq : (decide (c ≤ i) && a.testBit c) = true
    · have h1 : Nat.ble c i = true := by rw [Nat.ble_eq]; simp_all
      have h2 : a.testBit c = true := by simp_all
      rw [ite_eq_left hq, h1, h2]
      exact (stepQ_keep d c L _ i (by omega)).symm
    · have : (Bool.rec (motive := fun _ => Bool) false (a.testBit c) (Nat.ble c i)) = false := by
        cases h : Nat.ble c i
        · rfl
        · have := Nat.le_of_ble_eq_true h
          simp_all
      rw [this, ite_eq_right hq]

theorem foldl_congr_mem {f g : Nat → Nat → Nat} (l : List Nat) (h : ∀ j ∈ l, ∀ x, f x j = g x j)
    (x : Nat) : l.foldl f x = l.foldl g x := by
  induction l generalizing x with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [h j (List.mem_cons_self ..)]
    exact ih (fun k hk => h k (List.mem_cons_of_mem _ hk)) _

theorem pivK_eq (d c : Nat) (L : List (Nat × Nat)) (hL : L.length = d) (hc : c ≤ d) :
    pivK d c L = pivP d c L := by
  unfold pivK
  have := pivGo_eq d c L hL.le d 0 (by omega)
  rw [List.drop_zero] at this
  rw [this]
  unfold pivP
  have hsplit : List.range' 0 d = List.range' 0 c ++ List.range' (0 + c) (d - c) := by
    rw [List.range'_append_1]
    congr 1
    omega
  rw [hsplit, List.foldl_append, Nat.zero_add]
  have h0 : (List.range' 0 c).foldl (stepQ d c L) d = d := by
    rw [foldl_congr_mem (g := fun x _ => x) (List.range' 0 c) (fun j hj x => by
      have : j < c := by simp at hj; omega
      unfold stepQ
      simp [show ¬ c ≤ j by omega])]
    clear hsplit
    induction (List.range' 0 c) <;> simp_all
  rw [h0]
  apply foldl_congr_mem
  intro j hj x
  have : c ≤ j := by simp at hj; omega
  unfold stepQ
  simp [this]

theorem colK_eq (d c : Nat) (L : List (Nat × Nat)) (hL : L.length = d) (hc : c ≤ d) :
    colK d c L = colP d c L := by
  unfold colK colP
  rw [strictL_eq, pivK_eq d c L hL hc]
  cases h : Nat.blt (pivP d c L) d
  · have : ¬ pivP d c L < d := by
      intro h'
      have : Nat.blt (pivP d c L) d = true := by rw [Nat.blt_eq]; exact h'
      simp_all
    rw [ite_eq_right this]
  · have : pivP d c L < d := by rw [← Nat.blt_eq]; exact h
    rw [ite_eq_left this]
    rw [getPK_eq, getPK_eq]
    rcases (L.getD (pivP d c L) (0, 0)) with ⟨ap, rp⟩
    change elimK c ap rp (setPK (setPK L _ _) c (ap, rp)) = _
    rw [setPK_eq, setPK_eq, elimK_eq]
    simp [hL]


theorem eqLK_sound : ∀ {L L' : List (Nat × Nat)}, eqLK L L' = true → L = L'
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | (a, b) :: L, (a', b') :: L', h => by
    change Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (eqLK L L') (Nat.beq b b')) (Nat.beq a a') = true at h
    cases h1 : Nat.beq a a' <;> cases h2 : Nat.beq b b' <;> rw [h1, h2] at h <;>
      try exact absurd h Bool.false_ne_true
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, eqLK_sound h]


end CFSG.KS.SporSch.PF2

end
