module

public import CFSG.Sporadic.Fi24.MatSpec

public section

namespace CFSG.Sporadic.Fi24.Native

open Finset CFSG.F3.Native

@[expose] def vecW (a : W) : Fin 781 → ZMod 3 := fun j => a.val j.val

@[expose] noncomputable def rowSpan (r : ℕ) (X : Array W) : Submodule (ZMod 3) (Fin 781 → ZMod 3) :=
  Submodule.span (ZMod 3) (Set.range fun i : Fin r => vecW (rowW X i.val))

theorem vecW_add {a b : W} (ha : a.wf = true) (hb : b.wf = true) :
    vecW (a.add b) = vecW a + vecW b := by
  funext j; exact W.val_add ha hb j.val

theorem vecW_sub {a b : W} (ha : a.wf = true) (hb : b.wf = true) :
    vecW (a.sub b) = vecW a - vecW b := by
  funext j; exact W.val_sub ha hb j.val

theorem vecW_neg {a : W} (ha : a.wf = true) : vecW a.neg = -vecW a := by
  funext j; exact W.val_neg ha j.val


theorem mem_rowSpan {r : ℕ} (X : Array W) (i : Fin r) : vecW (rowW X i.val) ∈ rowSpan r X :=
  Submodule.subset_span ⟨i, rfl⟩

private theorem sub_eq_add_two : ∀ x y : ZMod 3, x - y = x + 2 * y := by decide

theorem rowSpan_eq_of_addRow {r : ℕ} {X Y : Array W} (k : Fin r)
    (hk : vecW (rowW Y k.val) = vecW (rowW X k.val))
    (h : ∀ i : Fin r, ∃ c : ZMod 3,
      vecW (rowW Y i.val) = vecW (rowW X i.val) + c • vecW (rowW X k.val)) :
    rowSpan r Y = rowSpan r X := by
  apply le_antisymm
  · unfold rowSpan
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := h i
    dsimp only
    rw [hc]
    exact Submodule.add_mem _ (mem_rowSpan X i) (Submodule.smul_mem _ c (mem_rowSpan X k))
  · unfold rowSpan
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := h i
    have e : vecW (rowW X i.val) = vecW (rowW Y i.val) - c • vecW (rowW Y k.val) := by
      rw [hk, hc]; abel
    dsimp only
    rw [e]
    exact Submodule.sub_mem _ (mem_rowSpan Y i) (Submodule.smul_mem _ c (mem_rowSpan Y k))

theorem rowSpan_eq_of_neg {r : ℕ} {X Y : Array W} (k : Fin r)
    (hk : vecW (rowW Y k.val) = -vecW (rowW X k.val))
    (h : ∀ i : Fin r, i ≠ k → vecW (rowW Y i.val) = vecW (rowW X i.val)) :
    rowSpan r Y = rowSpan r X := by
  have hk' : -vecW (rowW Y k.val) = vecW (rowW X k.val) := neg_eq_iff_eq_neg.2 hk
  have key : ∀ i : Fin r,
      vecW (rowW Y i.val) ∈ rowSpan r X ∧ vecW (rowW X i.val) ∈ rowSpan r Y := by
    intro i
    by_cases hi : i = k
    · subst hi
      refine ⟨?_, ?_⟩
      · rw [hk]; exact Submodule.neg_mem _ (mem_rowSpan X i)
      · rw [← hk']; exact Submodule.neg_mem _ (mem_rowSpan Y i)
    · rw [h i hi]
      exact ⟨mem_rowSpan X i, by rw [← h i hi]; exact mem_rowSpan Y i⟩
  apply le_antisymm
  · unfold rowSpan; rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (key i).1
  · unfold rowSpan; rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (key i).2

theorem rowSpan_swap {r : ℕ} {X : Array W} (hX : X.size = r) {i j : ℕ} (hi : i < r) (hj : j < r) :
    rowSpan r (X.swapIfInBounds i j) = rowSpan r X := by
  have hrow : ∀ k : Fin r, rowW (X.swapIfInBounds i j) k.val =
      rowW X (Equiv.swap (⟨i, hi⟩ : Fin r) ⟨j, hj⟩ k).val := by
    intro k
    unfold rowW
    rw [Array.getElem?_eq_getElem (by simp; omega),
      Array.getElem?_eq_getElem (by rw [hX]; exact Fin.isLt _), Option.getD_some,
      Option.getD_some, Array.getElem_swapIfInBounds]
    by_cases h1 : k.val = i
    · have : k = ⟨i, hi⟩ := Fin.ext h1
      subst this
      simp [Equiv.swap_apply_left, hX ▸ hj]
    · by_cases h2 : k.val = j
      · have : k = ⟨j, hj⟩ := Fin.ext h2
        subst this
        simp [Equiv.swap_apply_right, h1, hX ▸ hi]
      · have hne1 : k ≠ ⟨i, hi⟩ := fun e => h1 (congrArg Fin.val e)
        have hne2 : k ≠ ⟨j, hj⟩ := fun e => h2 (congrArg Fin.val e)
        simp [Equiv.swap_apply_of_ne_of_ne hne1 hne2, h1, h2]
  unfold rowSpan
  congr 1
  ext v
  simp only [Set.mem_range]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Equiv.swap (⟨i, hi⟩ : Fin r) ⟨j, hj⟩ k, by rw [hrow]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨Equiv.swap (⟨i, hi⟩ : Fin r) ⟨j, hj⟩ k, ?_⟩
    rw [hrow, Equiv.swap_apply_self]

theorem RowsWF.swapIfInBounds {X : Array W} (hX : RowsWF X) (i j : ℕ) :
    RowsWF (X.swapIfInBounds i j) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
  rw [Array.getElem_swapIfInBounds]
  split_ifs <;> exact hX _ (Array.getElem_mem _)

theorem RowsWF.modify {X : Array W} (hX : RowsWF X) (i : ℕ) {f : W → W}
    (hf : ∀ x, x.wf = true → (f x).wf = true) : RowsWF (X.modify i f) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
  rw [Array.getElem_modify]
  split_ifs
  · exact hf _ (hX _ (Array.getElem_mem _))
  · exact hX _ (Array.getElem_mem _)

theorem rowW_modify (X : Array W) (i : ℕ) (f : W → W) (k : ℕ) :
    rowW (X.modify i f) k = if i = k ∧ k < X.size then f (rowW X k) else rowW X k := by
  unfold rowW
  rw [Array.getElem?_modify]
  by_cases h : k < X.size
  · rw [Array.getElem?_eq_getElem h]
    split_ifs <;> simp_all
  · rw [Array.getElem?_eq_none (by omega)]
    split_ifs <;> simp_all

theorem rowW_elimRows (X : Array W) (r l : ℕ) (bit : UInt64) (pv : W) (h : ℕ) (hh : h < X.size) :
    rowW (elimRows X r l bit pv) h =
      if h = r then rowW X h
      else if (rowW X h).limbP l &&& bit != 0 then (rowW X h).sub pv
      else if (rowW X h).limbM l &&& bit != 0 then (rowW X h).add pv
      else rowW X h := by
  unfold elimRows rowW
  rw [Array.getElem?_mapIdx, Array.getElem?_eq_getElem hh]
  rfl

theorem elimRows_size (X : Array W) (r l : ℕ) (bit : UInt64) (pv : W) :
    (elimRows X r l bit pv).size = X.size := by
  unfold elimRows; simp

theorem RowsWF.elimRows {X : Array W} (hX : RowsWF X) (r l : ℕ) (bit : UInt64) {pv : W}
    (hpv : pv.wf = true) : RowsWF (Native.elimRows X r l bit pv) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
  have hk' : k < X.size := by rwa [elimRows_size] at hk
  have e : (Native.elimRows X r l bit pv)[k] = rowW (Native.elimRows X r l bit pv) k := by
    unfold rowW; rw [Array.getElem?_eq_getElem hk]; rfl
  rw [e, rowW_elimRows _ _ _ _ _ _ hk']
  have hxk := hX.row k
  split_ifs
  · exact hxk
  · exact W.wf_sub hxk hpv
  · exact W.wf_add hxk hpv
  · exact hxk

theorem elimStage_spec {X : Array W} (hX : RowsWF X) {r j : ℕ} (hr : r < X.size)
    (hj : j < X.size) (l : ℕ) (bit : UInt64) :
    let X1 := X.swapIfInBounds r j
    let X2 := if (X1[r]?.getD W.zero).limbM l &&& bit != 0 then X1.modify r W.neg else X1
    (elimRows X2 r l bit (X2[r]?.getD W.zero)).size = X.size ∧
      RowsWF (elimRows X2 r l bit (X2[r]?.getD W.zero)) ∧
      rowSpan X.size (elimRows X2 r l bit (X2[r]?.getD W.zero)) = rowSpan X.size X := by
  intro X1 X2
  have hX1s : X1.size = X.size := by simp [X1]
  have hX1w : RowsWF X1 := RowsWF.swapIfInBounds hX r j
  have hX1span : rowSpan X.size X1 = rowSpan X.size X := rowSpan_swap rfl hr hj
  have hX2s : X2.size = X.size := by simp only [X2]; split_ifs <;> simp [hX1s]
  have hX2w : RowsWF X2 := by
    simp only [X2]; split_ifs
    · exact RowsWF.modify hX1w r (fun x hx => W.wf_neg hx)
    · exact hX1w
  have hX2span : rowSpan X.size X2 = rowSpan X.size X1 := by
    simp only [X2]; split_ifs
    · refine rowSpan_eq_of_neg (r := X.size) ⟨r, hr⟩ ?_ ?_
      · rw [rowW_modify, ite_eq_left ⟨rfl, by rw [hX1s]; exact hr⟩]
        exact vecW_neg (hX1w.row r)
      · intro i hi
        rw [rowW_modify, ite_eq_right (fun e => hi (Fin.ext e.1.symm))]
    · rfl
  have hpvr : X2[r]?.getD W.zero = rowW X2 r := rfl
  have hpvw : (X2[r]?.getD W.zero).wf = true := hX2w.row r
  refine ⟨by rw [elimRows_size, hX2s], RowsWF.elimRows hX2w r _ _ hpvw, ?_⟩
  rw [← hX1span, ← hX2span]
  refine rowSpan_eq_of_addRow (r := X.size) ⟨r, hr⟩ ?_ ?_
  · rw [rowW_elimRows _ _ _ _ _ _ (by rw [hX2s]; exact hr), ite_eq_left rfl]
  · intro i
    rw [rowW_elimRows _ _ _ _ _ _ (by rw [hX2s]; exact i.isLt)]
    have hiw := hX2w.row i.val
    split_ifs
    · exact ⟨0, by simp⟩
    · exact ⟨2, by
        rw [vecW_sub hiw hpvw, hpvr]
        ext t
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact sub_eq_add_two _ _⟩
    · exact ⟨1, by rw [vecW_add hiw hpvw, hpvr]; simp⟩
    · exact ⟨0, by simp⟩

theorem colStep_spec (st : RRef) (hst : RowsWF st.rows) (c : ℕ) :
    (colStep st c).rows.size = st.rows.size ∧ RowsWF (colStep st c).rows ∧
      rowSpan st.rows.size (colStep st c).rows = rowSpan st.rows.size st.rows := by
  unfold colStep
  by_cases h1 : st.rank < st.rows.size
  · rw [ite_eq_left h1]
    dsimp only
    by_cases h2 : findPiv st.rows (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64) st.rank <
        st.rows.size
    · rw [ite_eq_left h2]
      exact elimStage_spec hst h1 h2 _ _
    · rw [ite_eq_right h2]
      exact ⟨rfl, hst, rfl⟩
  · rw [ite_eq_right h1]
    exact ⟨rfl, hst, rfl⟩

theorem rref_spec (d : ℕ) {X : Array W} (hX : RowsWF X) :
    (rref d X).rows.size = X.size ∧ RowsWF (rref d X).rows ∧
      rowSpan X.size (rref d X).rows = rowSpan X.size X := by
  unfold rref
  have key : ∀ n : ℕ, (Nat.fold n (fun c _ st => colStep st c) ⟨X, 0, #[]⟩).rows.size = X.size ∧
      RowsWF (Nat.fold n (fun c _ st => colStep st c) ⟨X, 0, #[]⟩).rows ∧
      rowSpan X.size (Nat.fold n (fun c _ st => colStep st c) ⟨X, 0, #[]⟩).rows =
        rowSpan X.size X := by
    intro n
    induction n with
    | zero => rw [Nat.fold_zero]; exact ⟨rfl, hX, rfl⟩
    | succ n ih =>
      rw [Nat.fold_succ]
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨g1, g2, g3⟩ := colStep_spec _ h2 n
      rw [h1] at g1 g3
      exact ⟨g1, g2, g3.trans h3⟩
  exact key d

section Unique

variable {K : Type*} [Field K] {r n : ℕ}

@[expose] def IsRREF (R : Fin r → Fin n → K) (p : Fin r → Fin n) : Prop :=
  StrictMono p ∧ (∀ i j, R i (p j) = if i = j then 1 else 0) ∧ ∀ i c, c < p i → R i c = 0

theorem IsRREF.eq_sum {R : Fin r → Fin n → K} {p : Fin r → Fin n} (h : IsRREF R p) {v : Fin n → K}
    (hv : v ∈ Submodule.span K (Set.range R)) : v = ∑ j, v (p j) • R j := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
  have hc : ∀ k, (∑ j, c j • R j) (p k) = c k := by
    intro k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp [h.2.1 k k]
    · intro j _ hjk
      simp [h.2.1 j k, hjk]
    · simp
  simp only [hc]

theorem IsRREF.zero_below {R : Fin r → Fin n → K} {p : Fin r → Fin n} (h : IsRREF R p)
    {v : Fin n → K} (hv : v ∈ Submodule.span K (Set.range R)) {i₀ : Fin r}
    (hmin : ∀ j < i₀, v (p j) = 0) {c : Fin n} (hc : c < p i₀) : v c = 0 := by
  rw [h.eq_sum hv, Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hj : j < i₀
  · rw [hmin j hj, zero_mul]
  · have : p i₀ ≤ p j := h.1.monotone (not_lt.1 hj)
    rw [h.2.2 j c (lt_of_lt_of_le hc this), mul_zero]

theorem IsRREF.pivot_mem {R R' : Fin r → Fin n → K} {p p' : Fin r → Fin n} (h : IsRREF R p)
    (h' : IsRREF R' p') (hs : Submodule.span K (Set.range R') ≤ Submodule.span K (Set.range R))
    (i : Fin r) : p' i ∈ Set.range p := by
  have hv : R' i ∈ Submodule.span K (Set.range R) := hs (Submodule.subset_span ⟨i, rfl⟩)
  have hne : ∃ j, R' i (p j) ≠ 0 := by
    by_contra hall
    push Not at hall
    have := h.eq_sum hv
    have h1 : R' i (p' i) = 1 := by rw [h'.2.1 i i, ite_eq_left rfl]
    rw [this, Finset.sum_apply] at h1
    simp [hall] at h1
  classical
  let j₀ := Finset.min' (Finset.univ.filter fun j => R' i (p j) ≠ 0)
    (by obtain ⟨j, hj⟩ := hne; exact ⟨j, by simp [hj]⟩)
  have hj₀ : R' i (p j₀) ≠ 0 := by
    have := Finset.min'_mem (Finset.univ.filter fun j => R' i (p j) ≠ 0)
      (by obtain ⟨j, hj⟩ := hne; exact ⟨j, by simp [hj]⟩)
    simpa using this
  have hmin : ∀ j < j₀, R' i (p j) = 0 := by
    intro j hj
    by_contra hne'
    have := Finset.min'_le (Finset.univ.filter fun j => R' i (p j) ≠ 0) j (by simp [hne'])
    exact absurd hj (not_lt.2 this)
  refine ⟨j₀, ?_⟩
  rcases lt_trichotomy (p j₀) (p' i) with hlt | heq | hgt
  · exact absurd (h'.2.2 i _ hlt) hj₀
  · exact heq
  · have := h.zero_below hv hmin hgt
    rw [h'.2.1 i i, ite_eq_left rfl] at this
    exact absurd this one_ne_zero

theorem IsRREF.unique {R R' : Fin r → Fin n → K} {p p' : Fin r → Fin n} (h : IsRREF R p)
    (h' : IsRREF R' p') (hs : Submodule.span K (Set.range R) = Submodule.span K (Set.range R')) :
    R = R' := by
  have hpp : p = p' := by
    refine (StrictMono.range_inj_of_wellFoundedLT h.1 h'.1).1 (le_antisymm ?_ ?_)
    · rintro _ ⟨i, rfl⟩; exact h'.pivot_mem h hs.le i
    · rintro _ ⟨i, rfl⟩; exact h.pivot_mem h' hs.ge i
  subst hpp
  funext i
  have hv : R' i ∈ Submodule.span K (Set.range R) := hs ▸ Submodule.subset_span ⟨i, rfl⟩
  rw [h.eq_sum hv]
  simp only [h'.2.1]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [Ne.symm hji]
  · simp

end Unique


end CFSG.Sporadic.Fi24.Native
