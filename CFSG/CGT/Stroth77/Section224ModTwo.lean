module

public import CFSG.CGT.Stroth77.Section224Extension

public section

namespace CFSG.CGT.Stroth77

open Matrix


theorem int_modEq_two_of_even_sub {a b : ℤ} (h : Even (b - a)) : a ≡ b [ZMOD 2] :=
  Int.modEq_iff_dvd.mpr (even_iff_two_dvd.mp h)

theorem mulVec_modEq_two {M M' : IntMat} {v w : Fin 3 → ℤ}
    (hM : ∀ i j, M i j ≡ M' i j [ZMOD 2]) (hv : ∀ i, v i ≡ w i [ZMOD 2]) (i : Fin 3) :
    (M *ᵥ v) i ≡ (M' *ᵥ w) i [ZMOD 2] := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  exact (((hM i 0).mul_right (v 0)).add ((hM i 1).mul_right (v 1))).add
    ((hM i 2).mul_right (v 2)) |>.trans
    ((((Int.ModEq.refl (M' i 0)).mul (hv 0)).add
      ((Int.ModEq.refl (M' i 1)).mul (hv 1))).add
      ((Int.ModEq.refl (M' i 2)).mul (hv 2)))


theorem ofCols_modTwo {c a b c' a' b' : Fin 3 → ℤ}
    (hc : ∀ i, c i ≡ c' i [ZMOD 2]) (ha : ∀ i, a i ≡ a' i [ZMOD 2])
    (hb : ∀ i, b i ≡ b' i [ZMOD 2]) :
    ∀ i j, ofCols c a b i j ≡ ofCols c' a' b' i j [ZMOD 2] := by
  intro i j
  fin_cases j
  · simpa [ofCols_apply] using hc i
  · simpa [ofCols_apply] using ha i
  · simpa [ofCols_apply] using hb i

theorem uMat_last_col_modTwo {cu cu' : Fin 3 → ℤ} {κ κ' : ℤ}
    (hcu : ∀ i, cu i ≡ cu' i [ZMOD 2]) (hκ : κ ≡ κ' [ZMOD 2]) :
    ∀ i, (((![0, 1, 0] : Fin 3 → ℤ) - κ • cu) i ≡
      ((![0, 1, 0] : Fin 3 → ℤ) - κ' • cu') i [ZMOD 2]) := by
  intro i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact (Int.ModEq.refl ((![0, 1, 0] : Fin 3 → ℤ) i)).sub (hκ.mul (hcu i))

theorem uMat_modTwo_type100 {cu : Fin 3 → ℤ} {κ : ℤ}
    (hcu : ∀ i, cu i ≡ (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2])
    (hκ : κ ≡ 0 [ZMOD 2]) :
    ∀ i j, uMat cu κ i j ≡ Type100.uM i j [ZMOD 2] := by
  change ∀ i j, ofCols cu ![κ, 0, 1]
      (((![0, 1, 0] : Fin 3 → ℤ) - κ • cu)) i j ≡
    ofCols (![1, 0, 0] : Fin 3 → ℤ) ![0, 0, 1]
      (((![0, 1, 0] : Fin 3 → ℤ) - (0 : ℤ) • (![1, 0, 0] : Fin 3 → ℤ))) i j [ZMOD 2]
  refine ofCols_modTwo hcu ?_ (uMat_last_col_modTwo hcu hκ)
  intro i
  fin_cases i
  · simpa using hκ
  · exact Int.ModEq.refl _
  · exact Int.ModEq.refl _

theorem tM_modTwo_type100 {c₁ c₂ A : Fin 3 → ℤ} {ρ : IntMat}
    (hc₁ : ∀ i, c₁ i ≡ (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2])
    (hc₂ : ∀ i, c₂ i ≡ (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2])
    (hA : ∀ i, A i ≡ (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2])
    (hρ : ρ = Type100.ρM) :
    ∀ i j, ofCols c₁ c₂ (ρ *ᵥ A) i j ≡ Type100.tM i j [ZMOD 2] := by
  have hcol : ∀ i, (ρ *ᵥ A) i ≡ (Type100.ρM *ᵥ (![2, 1, 2] : Fin 3 → ℤ)) i [ZMOD 2] := by
    subst hρ
    intro i
    exact mulVec_modEq_two (fun _ _ => Int.ModEq.refl _) hA i
  simpa only [Type100.tM, Type100.uvA] using ofCols_modTwo hc₁ hc₂ hcol

theorem uvM_modTwo_type100 {u A : Fin 3 → ℤ} {ρ tM : IntMat}
    (hu : ∀ i, u i ≡ (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2])
    (hA : ∀ i, A i ≡ (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2])
    (hρ : ρ = Type100.ρM)
    (ht : ∀ i j, tM i j ≡ Type100.tM i j [ZMOD 2]) :
    ∀ i j, ofCols u A (ρ *ᵥ (tM *ᵥ A)) i j ≡ Type100.uvM i j [ZMOD 2] := by
  have hcol : ∀ i, (ρ *ᵥ (tM *ᵥ A)) i ≡
      (Type100.ρM *ᵥ (Type100.tM *ᵥ (![2, 1, 2] : Fin 3 → ℤ))) i [ZMOD 2] := by
    subst hρ
    have htA : ∀ i, (tM *ᵥ A) i ≡ (Type100.tM *ᵥ (![2, 1, 2] : Fin 3 → ℤ)) i [ZMOD 2] :=
      fun i => mulVec_modEq_two ht hA i
    intro i
    exact mulVec_modEq_two (fun _ _ => Int.ModEq.refl _) htA i
  simpa only [Type100.uvM, Type100.uvA, Type100.tM] using ofCols_modTwo hu hA hcol

theorem modTwo_t100 (m : ℕ) :
    (∀ i j, (StrothTypeIndex.t100 m).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t100 m).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t100 m).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t100 m).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) :=
  ⟨fun _ _ => Int.ModEq.refl _, fun _ _ => Int.ModEq.refl _,
    fun _ _ => Int.ModEq.refl _, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t101 (s : ℕ) :
    (∀ i j, (StrothTypeIndex.t101 s).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t101 s).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t101 s).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t101 s).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  have hA : ∀ i, Type101.uvA s i ≡ (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type101.uvA]
  have hc₂ : ∀ i, (![0, -1 + 2 ^ (s + 1), 0] : Fin 3 → ℤ) i ≡
      (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have htM : ∀ i j, Type101.tM s i j ≡ Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![1, 2, 0]) (c₂ := ![0, -1 + 2 ^ (s + 1), 0])
      (A := Type101.uvA s) (ρ := Type101.ρM s) (fun i => Int.ModEq.refl _) hc₂ hA rfl
    simpa only [Type101.tM] using h
  have huvM : ∀ i j, Type101.uvM s i j ≡ Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-3, -2, -2]) (A := Type101.uvA s)
      (ρ := Type101.ρM s) (tM := Type101.tM s) (fun i => Int.ModEq.refl _) hA rfl htM
    simpa only [Type101.uvM] using h
  have huM : ∀ i j, Type101.uM s i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![1, 0, 0]) (κ := 0)
      (fun i => Int.ModEq.refl _) (Int.ModEq.refl (0 : ℤ))
    simpa only [Type101.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t110 (t : ℕ) :
    (∀ i j, (StrothTypeIndex.t110 t).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t110 t).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t110 t).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t110 t).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  have hu : ∀ i, (![-3, -2 + 2 ^ (t + 2), -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have hc₁ : ∀ i, (![1, 2, 2 ^ (t + 2)] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have htM : ∀ i j, Type110.tM t i j ≡ Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![1, 2, 2 ^ (t + 2)]) (c₂ := ![0, -1, 0])
      (A := Type110.uvA t) (ρ := Type110.ρM t)
      hc₁ (fun i => Int.ModEq.refl _) (fun i => Int.ModEq.refl _) rfl
    simpa only [Type110.tM] using h
  have huvM : ∀ i j, Type110.uvM t i j ≡ Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-3, -2 + 2 ^ (t + 2), -2]) (A := Type110.uvA t)
      (ρ := Type110.ρM t) (tM := Type110.tM t)
      hu (fun i => Int.ModEq.refl _) rfl htM
    simpa only [Type110.uvM] using h
  have hcu : ∀ i, (![1 + 2 ^ (t + 1), 0, 0] : Fin 3 → ℤ) i ≡
      (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have huM : ∀ i j, Type110.uM t i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![1 + 2 ^ (t + 1), 0, 0]) (κ := 0)
      hcu (Int.ModEq.refl (0 : ℤ))
    simpa only [Type110.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t111 (t : ℕ) :
    (∀ i j, (StrothTypeIndex.t111 t).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t111 t).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t111 t).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t111 t).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  have hu : ∀ i, (![-3, -2 + 2 ^ (t + 2), -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have hA : ∀ i, Type111.uvA t i ≡ (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type111.uvA]
  have hc₁ : ∀ i, (![1, 2, 2 ^ (t + 2)] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have hc₂ : ∀ i, (![0, -1 + 2 ^ (t + 2), 0] : Fin 3 → ℤ) i ≡
      (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have htM : ∀ i j, Type111.tM t i j ≡ Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![1, 2, 2 ^ (t + 2)])
      (c₂ := ![0, -1 + 2 ^ (t + 2), 0]) (A := Type111.uvA t) (ρ := Type111.ρM t)
      hc₁ hc₂ hA rfl
    simpa only [Type111.tM] using h
  have huvM : ∀ i j, Type111.uvM t i j ≡ Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-3, -2 + 2 ^ (t + 2), -2]) (A := Type111.uvA t)
      (ρ := Type111.ρM t) (tM := Type111.tM t)
      hu hA rfl htM
    simpa only [Type111.uvM] using h
  have hcu : ∀ i, (![1 + 2 ^ (t + 1), 0, 0] : Fin 3 → ℤ) i ≡
      (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have huM : ∀ i j, Type111.uM t i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![1 + 2 ^ (t + 1), 0, 0]) (κ := 0)
      hcu (Int.ModEq.refl (0 : ℤ))
    simpa only [Type111.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t120 (m : ℕ) (hm : 3 ≤ m) :
    (∀ i j, (StrothTypeIndex.t120 m hm).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t120 m hm).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t120 m hm).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t120 m hm).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  obtain ⟨hi, hF, -⟩ := Type120.data m (by omega)
  have hu : ∀ i, (![-Type120.iV (m + 1), 2, -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have hA : ∀ i, Type120.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) i ≡
      (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type120.uvA]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type120.uvA, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type120.uvA]
  have hc₁ : ∀ i, (![4 - Type120.iV (m + 1), 2, 4] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have hc₂ : ∀ i,
      (![4 * Type120.GV (m + 1) * Type120.iV (m + 1), -7 * Type120.iV (m + 1),
        -8 * Type120.iV (m + 1)] : Fin 3 → ℤ) i ≡ (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have htM : ∀ i j,
      Type120.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) i j ≡
        Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![4 - Type120.iV (m + 1), 2, 4])
      (c₂ := ![4 * Type120.GV (m + 1) * Type120.iV (m + 1), -7 * Type120.iV (m + 1),
        -8 * Type120.iV (m + 1)])
      (A := Type120.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1))) (ρ := Type120.ρM)
      hc₁ hc₂ hA rfl
    simpa only [Type120.tM] using h
  have huvM : ∀ i j,
      Type120.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) i j ≡
        Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-Type120.iV (m + 1), 2, -2])
      (A := Type120.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1))) (ρ := Type120.ρM)
      (tM := Type120.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)))
      hu hA rfl htM
    simpa only [Type120.uvM] using h
  have hcu : ∀ i, (![-1, 0, 0] : Fin 3 → ℤ) i ≡ (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have hκ : (-4 * Type120.FV (m + 1) : ℤ) ≡ 0 [ZMOD 2] := by
    apply int_modEq_two_of_even_sub
    simp +decide [parity_simps]
  have huM : ∀ i j, Type120.uM (Type120.FV (m + 1)) i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![-1, 0, 0]) (κ := -4 * Type120.FV (m + 1)) hcu hκ
    simpa only [Type120.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t121 (m : ℕ) (hm : 3 ≤ m) :
    (∀ i j, (StrothTypeIndex.t121 m hm).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t121 m hm).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t121 m hm).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t121 m hm).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  obtain ⟨hi, hF, -, hK, -⟩ := Type121.data m (by omega)
  have hu : ∀ i, (![-Type120.iV (m + 1), 2, -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have hA : ∀ i, Type121.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m) i ≡
      (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type121.uvA]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type121.uvA, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type121.uvA, hK]
  have hc₁ : ∀ i, (![4 - Type120.iV (m + 1), 2, 4] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have hc₂ : ∀ i,
      (![4 * Type120.GV (m + 1) * Type120.iV (m + 1),
        -7 * Type120.iV (m + 1) + 2 ^ m,
        -8 * Type120.iV (m + 1)] : Fin 3 → ℤ) i ≡ (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi, hK]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have htM : ∀ i j,
      Type121.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![4 - Type120.iV (m + 1), 2, 4])
      (c₂ := ![4 * Type120.GV (m + 1) * Type120.iV (m + 1),
        -7 * Type120.iV (m + 1) + 2 ^ m, -8 * Type120.iV (m + 1)])
      (A := Type121.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m))
      (ρ := Type121.ρM) hc₁ hc₂ hA rfl
    simpa only [Type121.tM] using h
  have huvM : ∀ i j,
      Type121.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-Type120.iV (m + 1), 2, -2])
      (A := Type121.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m))
      (ρ := Type121.ρM)
      (tM := Type121.tM (Type120.iV (m + 1)) (Type120.FV (m + 1))
        (Type120.GV (m + 1)) (2 ^ m))
      hu hA rfl htM
    simpa only [Type121.uvM] using h
  have hcu : ∀ i, (![-1, 0, 0] : Fin 3 → ℤ) i ≡ (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have hκ : (-4 * Type120.FV (m + 1) : ℤ) ≡ 0 [ZMOD 2] := by
    apply int_modEq_two_of_even_sub
    simp +decide [parity_simps]
  have huM : ∀ i j, Type121.uM (Type120.FV (m + 1)) i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![-1, 0, 0]) (κ := -4 * Type120.FV (m + 1)) hcu hκ
    simpa only [Type121.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t130 (m : ℕ) (hm : 3 ≤ m) :
    (∀ i j, (StrothTypeIndex.t130 m hm).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t130 m hm).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t130 m hm).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t130 m hm).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := Type130.data m (by omega)
  have hu : ∀ i, (![-Type120.iV (m + 1), 2 + 2 ^ m, -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hK]
    · exact Int.ModEq.refl _
  have hA : ∀ i, Type130.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) i ≡
      (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type130.uvA]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type130.uvA, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type130.uvA]
  have hc₁ : ∀ i, (![4 - Type120.iV (m + 1), 2, 4 + 2 ^ m] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hK]
  have hc₂ : ∀ i,
      (![4 * Type120.GV (m + 1) * Type120.iV (m + 1), -7 * Type120.iV (m + 1),
        -8 * Type120.iV (m + 1)] : Fin 3 → ℤ) i ≡ (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have htM : ∀ i j,
      Type130.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![4 - Type120.iV (m + 1), 2, 4 + 2 ^ m])
      (c₂ := ![4 * Type120.GV (m + 1) * Type120.iV (m + 1), -7 * Type120.iV (m + 1),
        -8 * Type120.iV (m + 1)])
      (A := Type130.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1))) (ρ := Type130.ρM)
      hc₁ hc₂ hA rfl
    simpa only [Type130.tM] using h
  have huvM : ∀ i j,
      Type130.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-Type120.iV (m + 1), 2 + 2 ^ m, -2])
      (A := Type130.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1))) (ρ := Type130.ρM)
      (tM := Type130.tM (Type120.iV (m + 1)) (Type120.FV (m + 1))
        (Type120.GV (m + 1)) (2 ^ m))
      hu hA rfl htM
    simpa only [Type130.uvM] using h
  have hcu : ∀ i, (![-1 + 2 ^ (m - 1), 0, 0] : Fin 3 → ℤ) i ≡
      (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hJ]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have hκ : (-4 * Type120.FV (m + 1) : ℤ) ≡ 0 [ZMOD 2] := by
    apply int_modEq_two_of_even_sub
    simp +decide [parity_simps]
  have huM : ∀ i j,
      Type130.uM (Type120.FV (m + 1)) (2 ^ (m - 1)) i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![-1 + 2 ^ (m - 1), 0, 0])
      (κ := -4 * Type120.FV (m + 1)) hcu hκ
    simpa only [Type130.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t131 (m : ℕ) (hm : 3 ≤ m) :
    (∀ i j, (StrothTypeIndex.t131 m hm).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t131 m hm).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t131 m hm).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t131 m hm).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := Type131.data m (by omega)
  have hu : ∀ i, (![-Type120.iV (m + 1), 2 + 2 ^ m, -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hK]
    · exact Int.ModEq.refl _
  have hA : ∀ i, Type131.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m) i ≡
      (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type131.uvA]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type131.uvA, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type131.uvA, hK]
  have hc₁ : ∀ i, (![4 - Type120.iV (m + 1), 2, 4 + 2 ^ m] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hK]
  have hc₂ : ∀ i,
      (![4 * Type120.GV (m + 1) * Type120.iV (m + 1),
        -7 * Type120.iV (m + 1) + 2 ^ m,
        -8 * Type120.iV (m + 1)] : Fin 3 → ℤ) i ≡ (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi, hK]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have htM : ∀ i j,
      Type131.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![4 - Type120.iV (m + 1), 2, 4 + 2 ^ m])
      (c₂ := ![4 * Type120.GV (m + 1) * Type120.iV (m + 1),
        -7 * Type120.iV (m + 1) + 2 ^ m, -8 * Type120.iV (m + 1)])
      (A := Type131.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m))
      (ρ := Type131.ρM) hc₁ hc₂ hA rfl
    simpa only [Type131.tM] using h
  have huvM : ∀ i j,
      Type131.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-Type120.iV (m + 1), 2 + 2 ^ m, -2])
      (A := Type131.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m))
      (ρ := Type131.ρM)
      (tM := Type131.tM (Type120.iV (m + 1)) (Type120.FV (m + 1))
        (Type120.GV (m + 1)) (2 ^ m))
      hu hA rfl htM
    simpa only [Type131.uvM] using h
  have hcu : ∀ i, (![-1 + 2 ^ (m - 1), 0, 0] : Fin 3 → ℤ) i ≡
      (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hJ]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have hκ : (-4 * Type120.FV (m + 1) : ℤ) ≡ 0 [ZMOD 2] := by
    apply int_modEq_two_of_even_sub
    simp +decide [parity_simps]
  have huM : ∀ i j,
      Type131.uM (Type120.FV (m + 1)) (2 ^ (m - 1)) i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![-1 + 2 ^ (m - 1), 0, 0])
      (κ := -4 * Type120.FV (m + 1)) hcu hκ
    simpa only [Type131.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩


end CFSG.CGT.Stroth77
