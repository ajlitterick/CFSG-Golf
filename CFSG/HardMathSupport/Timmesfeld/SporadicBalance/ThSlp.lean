
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpBase

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase1
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CoreByList
public import CFSG.Sporadic.ThSchreier.AutAssembly

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

theorem matJ_injective : Function.Injective matJ := fun g h hgh =>
  Subtype.ext (Units.ext hgh)

theorem card_centralizer_conj_eq (g s : J) :
    Nat.card (Subgroup.centralizer ({g * s * g⁻¹} : Set J)) =
      Nat.card (Subgroup.centralizer ({s} : Set J)) := by
  rw [← CFSG.Sporadic.ThSchreier.centralizer_map_conj g s]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem eq_of_rowsMatrix_eq {X Y : Array V4} {g h : J} (hX : rowsMatrix X = matJ g)
    (hY : rowsMatrix Y = matJ h) (e : eqRows X Y = true) : g = h :=
  matJ_injective (by rw [← hX, ← hY, eqRows_iff.1 e])

theorem ne_of_rowsDiffer {X Y : Array V4} {g h : J} (hX : rowsMatrix X = matJ g)
    (hY : rowsMatrix Y = matJ h) (e : rowsDiffer X Y = true) : g ≠ h := by
  rintro rfl
  exact rowsMatrix_ne_of_rowsDiffer e (hX.trans hY.symm)

@[expose] noncomputable def opJ (R : ℕ → J) : Op → ℕ → J
  | .mul i j k => Function.update R k (R i * R j)
  | .pow e i k => Function.update R k (R i ^ e)

@[expose] noncomputable def initJ (g h : J) : ℕ → J := fun r =>
  if r = 0 then g else if r = 1 then h else 1

@[expose] noncomputable def slpJ (g h : J) (prog : List Op) : ℕ → J :=
  prog.foldl opJ (initJ g h)

theorem rowsMatrix_slpRows {A B : Array V4} {g h : J} (hA : rowsMatrix A = matJ g)
    (hB : rowsMatrix B = matJ h) {n : ℕ} {prog : List Op} (hprog : prog.all (Op.lt n) = true) :
    (slpRows A B n prog).size = n ∧
      ∀ r < n, rowsMatrix (slpRows A B n prog)[r]! = matJ (slpJ g h prog r) := by
  suffices H : ∀ (prog : List Op), prog.all (Op.lt n) = true →
      ∀ (R : Array (Array V4)) (RJ : ℕ → J), R.size = n →
        (∀ r < n, rowsMatrix R[r]! = matJ (RJ r)) →
        (prog.foldl opRows R).size = n ∧
          ∀ r < n, rowsMatrix (prog.foldl opRows R)[r]! = matJ (prog.foldl opJ RJ r) by
    refine H prog hprog _ _ (by simp [initRows]) fun r hr => ?_
    rw [initRows, getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
    simp only [initJ]
    split_ifs
    · exact hA
    · exact hB
    · rw [matJ_one]; exact rowsMatrix_idRows
  intro prog
  induction prog with
  | nil => intro _ R RJ hs hR; exact ⟨hs, hR⟩
  | cons op prog ih =>
    intro hp R RJ hs hR
    simp only [List.all_cons, Bool.and_eq_true] at hp
    refine ih hp.2 _ _ (by rw [opRows_size, hs]) fun r hr => ?_
    have hr' : r < R.size := hs ▸ hr
    cases op with
    | mul i j k =>
      have hp1 := hp.1
      simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hp1
      obtain ⟨⟨hi, hj⟩, -⟩ := hp1
      simp only [opRows, opJ]
      rw [getElem!_setIfInBounds_of_lt hr']
      by_cases hkr : k = r
      · subst hkr
        rw [if_pos rfl, Function.update_self, rowsMatrix_mulRows, hR i hi, hR j hj, matJ_mul]
      · rw [if_neg hkr, Function.update_of_ne (Ne.symm hkr), hR r hr]
    | pow e i k =>
      have hp1 := hp.1
      simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hp1
      obtain ⟨hi, -⟩ := hp1
      simp only [opRows, opJ]
      rw [getElem!_setIfInBounds_of_lt hr']
      by_cases hkr : k = r
      · subst hkr
        rw [if_pos rfl, Function.update_self, rowsMatrix_powRowsN, hR i hi, matJ_pow]
      · rw [if_neg hkr, Function.update_of_ne (Ne.symm hkr), hR r hr]

theorem rowsMatrix_wordRowsL {gs : Array (Array V4)} {R : ℕ → J} {w : List ℕ}
    (h : ∀ r ∈ w, rowsMatrix gs[r]! = matJ (R r)) :
    rowsMatrix (wordRowsL gs w) = matJ (w.map R).prod := by
  suffices H : ∀ (w : List ℕ), (∀ r ∈ w, rowsMatrix gs[r]! = matJ (R r)) →
      ∀ acc : Array V4, rowsMatrix (w.foldl (fun acc r => mulRows acc gs[r]!) acc) =
        rowsMatrix acc * matJ (w.map R).prod by
    rw [wordRowsL, H w h, rowsMatrix_idRows, one_mul]
  intro w
  induction w with
  | nil => intro _ acc; simp [matJ_one]
  | cons r w ih =>
    intro hw acc
    rw [List.foldl_cons, ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)), rowsMatrix_mulRows,
      hw r List.mem_cons_self, mul_assoc, ← matJ_mul]
    simp

theorem pairOK_spec {X Y : Array V4} {x y : J} (hX : rowsMatrix X = matJ x)
    (hY : rowsMatrix Y = matJ y) {p : ℕ} (h : pairOK X Y p = true) :
    x ^ p = 1 ∧ y ^ p = 1 ∧ matJ x * matJ y = matJ y * matJ x ∧ x ≠ 1 ∧ ∀ k < p, y ≠ x ^ k := by
  unfold pairOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hone : rowsMatrix idRows = matJ 1 := by rw [rowsMatrix_idRows, matJ_one]
  refine ⟨eq_of_rowsMatrix_eq (by rw [rowsMatrix_powRowsN, hX, matJ_pow]) hone h1,
    eq_of_rowsMatrix_eq (by rw [rowsMatrix_powRowsN, hY, matJ_pow]) hone h2, ?_,
    ne_of_rowsDiffer hX hone h4, fun k hk => ?_⟩
  · rw [← hX, ← hY, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, eqRows_iff.1 h3]
  · exact ne_of_rowsDiffer hY (by rw [rowsMatrix_powRowsN, hX, matJ_pow]) (h5 k hk)


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
