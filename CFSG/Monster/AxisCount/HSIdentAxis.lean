module

public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.AxisCount.AxisFacts
public import CFSG.Monster.AxisCount.SchreierBasic
public import Certificates.Data.CFSGNative.MonsterAxis.HSEval

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.HS

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.B.Short CFSG.Monster.B CFSG.Monster.B.Rep4371

theorem getD_ite_modify (D : Array ℤ) (hD : D.size = 196884) (t : ℕ × ℤ) (k : ℕ)
    (hk : k < 196884) :
    (if t.1 < 196884 then D.modify t.1 (fun y => y + t.2) else D).getD k 0 =
      D.getD k 0 + if t.1 = k ∧ t.1 < 196884 then t.2 else 0 := by
  by_cases h1 : t.1 < 196884
  · rw [ite_eq_left h1]
    have hk' : k < D.size := by omega
    have hk'' : k < (D.modify t.1 (fun y => y + t.2)).size := by simpa using hk'
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk'',
      Array.getElem?_eq_getElem hk', Array.getElem_modify]
    by_cases h2 : t.1 = k
    · subst h2
      simp [h1]
    · simp [h2, h1]
  · simp [h1]

theorem foldl_getD (l : List (ℕ × ℤ)) (D : Array ℤ) (hD : D.size = 196884) (k : ℕ)
    (hk : k < 196884) :
    (l.foldl (fun D t => if t.1 < 196884 then D.modify t.1 (fun y => y + t.2) else D) D).getD k 0
      = D.getD k 0 + (l.map fun t => if t.1 = k ∧ t.1 < 196884 then t.2 else 0).sum := by
  induction l generalizing D with
  | nil => simp
  | cons t l ih =>
    have hsz : (if t.1 < 196884 then D.modify t.1 (fun y => y + t.2) else D).size = 196884 := by
      split_ifs <;> simp [hD]
    rw [List.foldl_cons, ih _ hsz, getD_ite_modify D hD t k hk, List.map_cons, List.sum_cons]
    ring

theorem ofList_getD (l : List (ℕ × ℤ)) (k : ℕ) (hk : k < 196884) :
    (Native.DVec.ofList l).D.getD k 0 =
      (l.map fun t => if t.1 = k ∧ t.1 < 196884 then t.2 else 0).sum := by
  unfold Native.DVec.ofList Native.DVec.ofListE
  rw [foldl_getD l _ (by simp) k hk]
  simp [Array.getD_eq_getD_getElem?, hk]

@[expose] def axisDVec (s : ℤ) : Native.DVec :=
  Native.DVec.ofList [(0, 1), (1, 1), (24, -1), (300, s)]

theorem axisDVec_e (s : ℤ) : (axisDVec s).e = 0 := rfl

theorem aIdx_char : ∀ i j : Fin 24,
    ((if 0 = Native.aIdx i j then (1 : ℤ) else 0) + (if 1 = Native.aIdx i j then 1 else 0) +
      (if 24 = Native.aIdx i j then -1 else 0)) =
    ((if i = 0 then 1 else 0) - (if i = 1 then 1 else 0)) *
      ((if j = 0 then 1 else 0) - (if j = 1 then 1 else 0)) := by
  decide

theorem axisDVec_getD (s : ℤ) (k : ℕ) (hk : k < 196884) :
    (axisDVec s).D.getD k 0 =
      (if 0 = k then 1 else 0) + (if 1 = k then 1 else 0) + (if 24 = k then -1 else 0) +
        (if 300 = k then s else 0) := by
  unfold axisDVec
  rw [ofList_getD _ k hk]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.reduceLT,
    and_true]
  ring

theorem interpA_axisDVec (s : ℤ) :
    ((interpA (axisDVec s) : symMat) : Matrix (Fin 24) (Fin 24) ℚ) =
      (2 : ℚ) • projMat (vMinus 0 1) := by
  ext i j
  have h300 : Native.aIdx i j < 300 := (Native.aIdx_spec i j i.2 j.2).1
  have e := axisDVec_getD s (Native.aIdx i j) (by omega)
  have h3 : ¬ 300 = Native.aIdx i j := by omega
  have key := aIdx_char i j
  simp only [h3, ite_false, add_zero] at e
  have hz : ((axisDVec s).D.getD (Native.aIdx i j) 0 : ℤ) =
      ((if i = 0 then 1 else 0) - (if i = 1 then 1 else 0)) *
        ((if j = 0 then 1 else 0) - (if j = 1 then 1 else 0)) := by
    rw [e]
    exact key
  simp only [interpA, Matrix.of_apply, axisDVec_e, pow_zero, div_one, Matrix.smul_apply,
    projMat, Matrix.vecMulVec_apply, smul_eq_mul, vMinus_zero_one, ratVec, eℤ, Pi.sub_apply,
    Pi.smul_apply, Pi.single_apply]
  rw [hz]
  split_ifs <;> simp_all <;> norm_num

theorem pairTab_zero : Native.pairTab[0]! = (0, 1) := by decide +kernel

theorem shortOf_zero_eq :
    shortOf ⟨0, by norm_num⟩ = ⟨coordOf rStar, isShortCoord_rStar⟩ := by
  apply Subtype.ext
  have h1 := keyOf_pair 0 (by norm_num)
  have h2 := pauliQ_minus (i := 0) (j := 1) (by decide)
  have h3 := coordOf_pauliQ
    ⟨false, 0, Model.dualN (2 ^ ((0 : Fin 24) : ℕ) ||| 2 ^ ((1 : Fin 24) : ℕ))⟩
  rw [h2] at h3
  have h4 : coordOf rStar = coordOf (rMinus 0 1) := rfl
  have h5 : coordOf rStar = (toC (keyOf 0).1, toD (keyOf 0).2) := by
    rw [h4, h3, h1, pairTab_zero]
    simp [toC_zero]
  exact h5.symm

theorem posOf_eq_zero_iff (c : ShortIdx) :
    posOf c = 0 ↔ c = ⟨coordOf rStar, isShortCoord_rStar⟩ := by
  constructor
  · intro h
    have h' : (⟨posOf c, posOf_lt c⟩ : Fin 98280) = ⟨0, by norm_num⟩ := Fin.ext h
    calc c = shortOf ⟨posOf c, posOf_lt c⟩ := (shortOf_posOf c).symm
      _ = shortOf ⟨0, by norm_num⟩ := by rw [h']
      _ = _ := shortOf_zero_eq
  · intro h
    have h' := posOf_shortOf (⟨0, by norm_num⟩ : Fin 98280)
    rw [shortOf_zero_eq] at h'
    rw [h]
    simpa using h'

theorem interpX_axisDVec (s : ℤ) :
    interpX (axisDVec s) = (s : ℚ) • Xlift rStar := by
  funext c
  have hq := posOf_lt c
  have e := axisDVec_getD s (300 + posOf c) (by omega)
  have h0 : ¬ 0 = 300 + posOf c := by omega
  have h1 : ¬ 1 = 300 + posOf c := by omega
  have h24 : ¬ 24 = 300 + posOf c := by omega
  simp only [h0, h1, h24, ite_false, add_zero, zero_add] at e
  have hc0 : centralCoord rStar = 0 := centralCoord_rMinus 0 1
  have hX : Xlift rStar = Pi.single ⟨coordOf rStar, isShortCoord_rStar⟩ 1 := by
    rw [Xlift_eq isShortCoord_rStar, hc0]
    simp [sgn]
  rw [hX]
  simp only [interpX, axisDVec_e, pow_zero, div_one, e, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul]
  by_cases hc : posOf c = 0
  · have hc' := (posOf_eq_zero_iff c).1 hc
    have h300 : (300 = 300 + posOf c) := by omega
    rw [ite_eq_left h300, ite_eq_left hc']
    simp
  · have hc' : ¬ c = ⟨coordOf rStar, isShortCoord_rStar⟩ :=
      fun h => hc ((posOf_eq_zero_iff c).2 h)
    have h300 : ¬ (300 = 300 + posOf c) := by omega
    rw [ite_eq_right h300, ite_eq_right hc']
    simp

theorem interpW_axisDVec (s : ℤ) : interpW (axisDVec s) = 0 := by
  funext r j
  have hr := rowOf_lt r
  have hj := j.2
  have e := axisDVec_getD s (98580 + 24 * rowOf r + j) (by omega)
  have h0 : ¬ 0 = 98580 + 24 * rowOf r + j := by omega
  have h1 : ¬ 1 = 98580 + 24 * rowOf r + j := by omega
  have h24 : ¬ 24 = 98580 + 24 * rowOf r + j := by omega
  have h300 : ¬ 300 = 98580 + 24 * rowOf r + j := by omega
  simp only [h0, h1, h24, h300, ite_false, add_zero] at e
  show (((axisDVec s).D.getD (98580 + 24 * rowOf r + j) 0 : ℤ) : ℚ) / 2 ^ (axisDVec s).e = 0
  rw [e]
  simp

theorem interp_axisDVec (s : ℤ) :
    interp (axisDVec s) =
      ((2 : ℚ) • ((axisE rStar, 0, 0) : SpaceB) + (s : ℚ) • ((0, Xlift rStar, 0) : SpaceB)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Subtype.ext
    rw [show (interp (axisDVec s)).1 = interpA (axisDVec s) from rfl, interpA_axisDVec]
    simp only [Prod.fst_add, Prod.smul_fst, Submodule.coe_add, Submodule.coe_smul]
    rw [coe_axisE_rStar]
    simp
  · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst]
    show interpX (axisDVec s) = _
    rw [interpX_axisDVec]
    simp
  · simp only [Prod.snd_add, Prod.smul_snd]
    show interpW (axisDVec s) = _
    rw [interpW_axisDVec]
    simp

@[expose] def axisP : Native.DVec := axisDVec (-2)

@[expose] def axisM : Native.DVec := axisDVec 2

theorem interp_axisP : interp axisP = aStar := by
  rw [axisP, interp_axisDVec, aStar_eq]
  ext <;> simp [sub_eq_add_neg]

theorem interp_axisM : interp axisM = aStarMinus := by
  rw [axisM, interp_axisDVec, aStarMinus, axis_zQ_mul isShortCoord_rStar]
  simp


@[expose] def hsCtx : Native.Ctx := Native.mkCtx ()

@[expose] def eqCheck (c : Native.Ctx) (w₁ : List Native.Gen) (v₁ : Native.DVec)
    (w₂ : List Native.Gen) (v₂ : Native.DVec) : Bool :=
  w₁.all Native.Gen.validB && w₂.all Native.Gen.validB &&
    (Native.evalWordC c w₁ v₁).eqv (Native.evalWordC c w₂ v₂)

theorem eqCheck_sound {w₁ w₂ : List Native.Gen} {v₁ v₂ : Native.DVec}
    (h : eqCheck hsCtx w₁ v₁ w₂ v₂ = true) :
    wordLin w₁ (interp v₁) = wordLin w₂ (interp v₂) := by
  have e : hsCtx = Native.mkCtx () := rfl
  rw [e] at h
  unfold eqCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hv₁, hv₂⟩, he⟩ := h
  have hw₁ : ∀ g ∈ w₁, g.validB = true := fun g hg => List.all_eq_true.1 hv₁ g hg
  have hw₂ : ∀ g ∈ w₂, g.validB = true := fun g hg => List.all_eq_true.1 hv₂ g hg
  rw [← evalWordC_sound w₁ hw₁ v₁, ← evalWordC_sound w₂ hw₂ v₂]
  exact eqv_sound he

@[expose] def xiGD : Native.GD := Native.GD.ofGen hsCtx Native.Gen.xi

@[expose] def p0Arr : Array Nat :=
  #[2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 12, 13, 17, 16, 19, 18, 23, 22, 21, 20]

@[expose] def p0GD : Native.GD := Native.GD.ofGen hsCtx (Native.Gen.perm p0Arr)

@[expose] def pw (w : List Native.Gen) : List Native.PGen :=
  Native.prepWordG hsCtx xiGD p0Arr p0GD w


theorem mem_range'_iff {lo hi r : Nat} : r ∈ List.range' lo (hi - lo) ↔ lo ≤ r ∧ r < hi := by
  rw [List.mem_range'_1]
  omega


theorem mem_bool (ε : Bool) : ε ∈ [true, false] := by cases ε <;> simp


@[expose] def isTauB : Native.Gen → Bool
  | .tau => true
  | _ => false


@[expose] def trA2N (d : Native.DVec) : ℤ :=
  ((List.range 24).map fun i =>
    ((List.range 24).map fun j => (d.D.getD (Native.aIdx i j) 0) ^ 2).sum).sum

theorem sum_range_map (f : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem trA2_interp
    (d : Native.DVec) : trA2 (interp d) = (trA2N d : ℚ) / 4 ^ d.e := by
  have h1 : trA2 (interp d) = ∑ i : Fin 24, ∑ j : Fin 24,
      ((d.D.getD (Native.aIdx i j) 0 : ℚ) / 2 ^ d.e) ^ 2 := rfl
  have h2 : trA2N d = ∑ i : Fin 24, ∑ j : Fin 24, (d.D.getD (Native.aIdx i j) 0) ^ 2 := by
    unfold trA2N
    simp only [sum_range_map]
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range]
  rw [h1, h2]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [div_pow, ← pow_mul, mul_comm, pow_mul]
  norm_num


end CFSG.Monster.AxisCount.HS
