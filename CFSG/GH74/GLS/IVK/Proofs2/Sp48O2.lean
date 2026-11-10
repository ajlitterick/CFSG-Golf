module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

open Matrix

namespace CFSG.GH74.GLS.IVK.Proofs2.Sp48

@[expose] def O2 (F : Type) [Field F] : Subgroup (GL (Fin 2) F) where
  carrier := {m | (m : Matrix (Fin 2) (Fin 2) F)ᵀ * (m : Matrix (Fin 2) (Fin 2) F) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul] at ha hb ⊢
    calc (↑b : Matrix (Fin 2) (Fin 2) F)ᵀ * (↑a)ᵀ * (↑a * ↑b)
        = (↑b)ᵀ * ((↑a)ᵀ * ↑a) * ↑b := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha, Matrix.mul_one, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h1 : ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = (a : Matrix (Fin 2) (Fin 2) F)ᵀ := by
      rw [Matrix.GeneralLinearGroup.coe_inv]
      exact Matrix.inv_eq_left_inv ha
    rw [h1, Matrix.transpose_transpose]
    exact mul_eq_one_comm.1 ha

@[expose] def GO2 (F : Type) [Field F] : Subgroup (GL (Fin 2) F) where
  carrier := {m | ∃ μ : F, μ ≠ 0 ∧
    (m : Matrix (Fin 2) (Fin 2) F)ᵀ * (m : Matrix (Fin 2) (Fin 2) F) = μ • (1 : Matrix (Fin 2) (Fin 2) F)}
  one_mem' := ⟨1, one_ne_zero, by simp⟩
  mul_mem' := by
    rintro a b ⟨μ, hμ, ha⟩ ⟨ν, hν, hb⟩
    refine ⟨μ * ν, mul_ne_zero hμ hν, ?_⟩
    simp only [Units.val_mul, Matrix.transpose_mul]
    calc (↑b : Matrix (Fin 2) (Fin 2) F)ᵀ * (↑a)ᵀ * (↑a * ↑b)
        = (↑b)ᵀ * ((↑a)ᵀ * ↑a) * ↑b := by simp only [Matrix.mul_assoc]
      _ = (μ * ν) • 1 := by
        rw [ha, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hb, smul_smul]
  inv_mem' := by
    rintro a ⟨μ, hμ, ha⟩
    refine ⟨μ⁻¹, inv_ne_zero hμ, ?_⟩
    have h0 : (μ⁻¹ • (a : Matrix (Fin 2) (Fin 2) F)ᵀ) * (a : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [Matrix.smul_mul, ha, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    have h1 : ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = μ⁻¹ • (a : Matrix (Fin 2) (Fin 2) F)ᵀ := by
      rw [Matrix.GeneralLinearGroup.coe_inv]
      exact Matrix.inv_eq_left_inv h0
    have h2 : (a : Matrix (Fin 2) (Fin 2) F) * (μ⁻¹ • (a : Matrix (Fin 2) (Fin 2) F)ᵀ) = 1 :=
      mul_eq_one_comm.1 h0
    rw [h1, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul, h2]

namespace O2Plane


section Entries

variable {F : Type} [Field F]

theorem transpose_mul_self_eq_smul_one_iff (M : Matrix (Fin 2) (Fin 2) F) (μ : F) :
    Mᵀ * M = μ • (1 : Matrix (Fin 2) (Fin 2) F) ↔
      M 0 0 ^ 2 + M 1 0 ^ 2 = μ ∧ M 0 0 * M 0 1 + M 1 0 * M 1 1 = 0 ∧
        M 0 1 ^ 2 + M 1 1 ^ 2 = μ := by
  constructor
  · intro h
    have h00 := congrFun₂ h 0 0
    have h01 := congrFun₂ h 0 1
    have h11 := congrFun₂ h 1 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
    refine ⟨by linear_combination h00, by linear_combination h01, by linear_combination h11⟩
  · rintro ⟨h1, h2, h3⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination h1
    · linear_combination h2
    · linear_combination h2
    · linear_combination h3

@[expose] def jm (F : Type) [Field F] : GL (Fin 2) F :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

@[expose] def sig (F : Type) [Field F] : GL (Fin 2) F :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem coe_jm : ((jm F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem coe_sig : ((sig F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

def Rx (F : Type) [Field F] : Subgroup (GL (Fin 2) F) := Subgroup.centralizer {jm F}

theorem mem_Rx_iff (m : GL (Fin 2) F) :
    m ∈ Rx F ↔ (m : Matrix (Fin 2) (Fin 2) F) 1 1 = (m : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      (m : Matrix (Fin 2) (Fin 2) F) 1 0 = -(m : Matrix (Fin 2) (Fin 2) F) 0 1 := by
  rw [Rx, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have h1 := h (jm F) (Set.mem_singleton _)
    have h1' := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) h1
    simp only [Units.val_mul, coe_jm] at h1'
    have e00 := congrFun₂ h1' 0 0
    have e01 := congrFun₂ h1' 0 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
    exact ⟨e01, e00⟩
  · rintro ⟨h1, h2⟩ x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    apply Units.ext
    simp only [Units.val_mul, coe_jm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2]

def SO2 (F : Type) [Field F] : Subgroup (GL (Fin 2) F) := O2 F ⊓ Rx F

theorem mem_SO2_iff (m : GL (Fin 2) F) :
    m ∈ SO2 F ↔ (m : Matrix (Fin 2) (Fin 2) F) 1 1 = (m : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      (m : Matrix (Fin 2) (Fin 2) F) 1 0 = -(m : Matrix (Fin 2) (Fin 2) F) 0 1 ∧
      (m : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 + (m : Matrix (Fin 2) (Fin 2) F) 0 1 ^ 2 = 1 := by
  rw [SO2, Subgroup.mem_inf, mem_Rx_iff]
  have h : m ∈ O2 F ↔ (m : Matrix (Fin 2) (Fin 2) F)ᵀ * (m : Matrix (Fin 2) (Fin 2) F) = 1 :=
    Iff.rfl
  rw [h, ← one_smul F (1 : Matrix (Fin 2) (Fin 2) F), transpose_mul_self_eq_smul_one_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    rw [h5] at h1
    exact ⟨h4, h5, by linear_combination h1⟩
  · rintro ⟨h4, h5, h1⟩
    refine ⟨⟨?_, ?_, ?_⟩, h4, h5⟩
    · rw [h5]; linear_combination h1
    · rw [h4, h5]; ring
    · rw [h4]; linear_combination h1

@[expose] def rotGL (a b : F) (h : a ^ 2 + b ^ 2 = 1) : GL (Fin 2) F :=
  ⟨!![a, b; -b, a], !![a, -b; b, a],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination h,
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination h⟩

theorem coe_rotGL (a b : F) (h : a ^ 2 + b ^ 2 = 1) :
    ((rotGL a b h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![a, b; -b, a] := rfl

theorem rotGL_mem (a b : F) (h : a ^ 2 + b ^ 2 = 1) : rotGL a b h ∈ SO2 F := by
  rw [mem_SO2_iff]
  simp only [coe_rotGL]
  exact ⟨rfl, rfl, h⟩

theorem sig_mul_self : sig F * sig F = 1 := by
  apply Units.ext
  simp only [Units.val_mul, coe_sig, Units.val_one]
  ext r c
  fin_cases r <;> fin_cases c <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sig_mem_O2 : sig F ∈ O2 F := by
  show (sig F : Matrix (Fin 2) (Fin 2) F)ᵀ * (sig F : Matrix (Fin 2) (Fin 2) F) = 1
  rw [coe_sig]
  ext r c
  fin_cases r <;> fin_cases c <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_sig : (sig F : Matrix (Fin 2) (Fin 2) F).det = -1 := by
  simp [coe_sig, Matrix.det_fin_two]

theorem sig_not_mem_Rx (h2 : (2 : F) ≠ 0) : sig F ∉ Rx F := by
  rw [mem_Rx_iff]
  rintro ⟨h1, h3⟩
  simp [coe_sig] at h3
  apply h2
  linear_combination h3

theorem exists_eq_of_mem_Rx {r : GL (Fin 2) F} (hr : r ∈ Rx F) :
    ∃ a b : F, (r : Matrix (Fin 2) (Fin 2) F) = !![a, b; -b, a] := by
  obtain ⟨h1, h2⟩ := (mem_Rx_iff _).1 hr
  refine ⟨(r : Matrix (Fin 2) (Fin 2) F) 0 0, (r : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2]

theorem sig_mul_mul_sig_mul {r : GL (Fin 2) F} (hr : r ∈ Rx F) :
    sig F * r * sig F * r =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det r) := by
  obtain ⟨a, b, hab⟩ := exists_eq_of_mem_Rx hr
  apply Units.ext
  simp only [Units.val_mul, coe_sig, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.val_det_apply, hab, Matrix.det_fin_two_of]
  ext c d
  fin_cases c <;> fin_cases d <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem mem_Rx_of_det_eq {g : GL (Fin 2) F} {μ : F} (hμ : μ ≠ 0)
    (h : (g : Matrix (Fin 2) (Fin 2) F)ᵀ * (g : Matrix (Fin 2) (Fin 2) F) = μ • 1)
    (hd : (g : Matrix (Fin 2) (Fin 2) F).det = μ) : g ∈ Rx F := by
  obtain ⟨e1, e2, -⟩ := (transpose_mul_self_eq_smul_one_iff _ μ).1 h
  rw [Matrix.det_fin_two] at hd
  rw [mem_Rx_iff]
  constructor
  · apply mul_left_cancel₀ hμ
    linear_combination (-((g : Matrix (Fin 2) (Fin 2) F) 1 1)) * e1 +
      (g : Matrix (Fin 2) (Fin 2) F) 1 0 * e2 + (g : Matrix (Fin 2) (Fin 2) F) 0 0 * hd
  · apply mul_left_cancel₀ hμ
    linear_combination (-((g : Matrix (Fin 2) (Fin 2) F) 0 1)) * e1 +
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 * e2 - (g : Matrix (Fin 2) (Fin 2) F) 1 0 * hd

theorem det_eq_or_neg {g : GL (Fin 2) F} {μ : F}
    (h : (g : Matrix (Fin 2) (Fin 2) F)ᵀ * (g : Matrix (Fin 2) (Fin 2) F) = μ • 1) :
    (g : Matrix (Fin 2) (Fin 2) F).det = μ ∨ (g : Matrix (Fin 2) (Fin 2) F).det = -μ := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one] at this
  simp only [Fintype.card_fin, mul_one] at this
  exact sq_eq_sq_iff_eq_or_eq_neg.1 (by linear_combination this)

theorem SO2_le_O2 : SO2 F ≤ O2 F := inf_le_left

theorem SO2_le_Rx : SO2 F ≤ Rx F := inf_le_right

theorem O2_le_GO2 : O2 F ≤ GO2 F := fun g hg => ⟨1, one_ne_zero, by rw [one_smul]; exact hg⟩

theorem GO2_cases {g : GL (Fin 2) F} (hg : g ∈ GO2 F) : g ∈ Rx F ∨ sig F * g ∈ Rx F := by
  obtain ⟨μ, hμ, h⟩ := hg
  rcases det_eq_or_neg h with hd | hd
  · exact Or.inl (mem_Rx_of_det_eq hμ h hd)
  · right
    refine mem_Rx_of_det_eq hμ ?_ ?_
    · have hs : (sig F : Matrix (Fin 2) (Fin 2) F)ᵀ * (sig F : Matrix (Fin 2) (Fin 2) F) = 1 :=
        sig_mem_O2
      simp only [Units.val_mul, Matrix.transpose_mul]
      calc (g : Matrix (Fin 2) (Fin 2) F)ᵀ * (sig F : Matrix (Fin 2) (Fin 2) F)ᵀ *
            ((sig F : Matrix (Fin 2) (Fin 2) F) * g)
          = (g : Matrix (Fin 2) (Fin 2) F)ᵀ * ((sig F : Matrix (Fin 2) (Fin 2) F)ᵀ *
            (sig F : Matrix (Fin 2) (Fin 2) F)) * g := by simp only [Matrix.mul_assoc]
        _ = μ • 1 := by rw [hs, Matrix.mul_one]; exact h
    · rw [Units.val_mul, Matrix.det_mul, det_sig, hd]
      ring

theorem O2_cases {g : GL (Fin 2) F} (hg : g ∈ O2 F) : g ∈ SO2 F ∨ sig F * g ∈ SO2 F := by
  rcases GO2_cases (O2_le_GO2 hg) with h | h
  · exact Or.inl ⟨hg, h⟩
  · exact Or.inr ⟨(O2 F).mul_mem sig_mem_O2 hg, h⟩

end Entries

section Count

variable {F : Type} [Field F]

abbrev Conic (F : Type) [Field F] : Type := {p : F × F // p.1 ^ 2 + p.2 ^ 2 = 1}

abbrev Stereo (F : Type) [Field F] : Type := {t : F // t ^ 2 + 1 ≠ 0}

theorem stereo_aux {a b : F} (h : a ^ 2 + b ^ 2 = 1) (ha : a ≠ -1) :
    (b / (a + 1)) ^ 2 + 1 = 2 / (a + 1) := by
  have ha' : a + 1 ≠ 0 := fun h0 => ha (by linear_combination h0)
  field_simp
  linear_combination h

open Classical in
noncomputable def conicEquiv (h2 : (2 : F) ≠ 0) : Conic F ≃ Option (Stereo F) where
  toFun p := if ha : p.1.1 = -1 then none else
    some ⟨p.1.2 / (p.1.1 + 1), by
      rw [stereo_aux p.2 ha]
      have ha' : p.1.1 + 1 ≠ 0 := fun h0 => ha (by linear_combination h0)
      exact div_ne_zero h2 ha'⟩
  invFun o := match o with
    | none => ⟨(-1, 0), by norm_num⟩
    | some t => ⟨((1 - t.1 ^ 2) / (t.1 ^ 2 + 1), 2 * t.1 / (t.1 ^ 2 + 1)), by
        have ht := t.2
        dsimp only
        field_simp
        ring⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    by_cases ha : a = -1
    · simp only [ha, dite_true]
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · have hb : b ^ 2 = 0 := by
          have h' : (-1 : F) ^ 2 + b ^ 2 = 1 := by simpa [ha] using h
          linear_combination h'
        have := pow_eq_zero_iff (two_ne_zero) |>.1 hb
        simp [this]
    · simp only [ha, dite_false]
      have ha' : a + 1 ≠ 0 := fun h0 => ha (by linear_combination h0)
      have key := stereo_aux h ha
      apply Subtype.ext
      apply Prod.ext
      · show (1 - (b / (a + 1)) ^ 2) / ((b / (a + 1)) ^ 2 + 1) = a
        rw [key]
        field_simp
        linear_combination (-1 : F) * h
      · show 2 * (b / (a + 1)) / ((b / (a + 1)) ^ 2 + 1) = b
        rw [key]
        field_simp
  right_inv := by
    rintro (_ | ⟨t, ht⟩)
    · simp
    · have hne : (1 - t ^ 2) / (t ^ 2 + 1) ≠ -1 := by
        intro h0
        field_simp at h0
        apply h2
        linear_combination h0
      simp only [hne, dite_false]
      apply congrArg
      apply Subtype.ext
      show 2 * t / (t ^ 2 + 1) / ((1 - t ^ 2) / (t ^ 2 + 1) + 1) = t
      rw [show (1 - t ^ 2) / (t ^ 2 + 1) + 1 = 2 / (t ^ 2 + 1) by field_simp; ring]
      field_simp

theorem isSquare_neg_one_iff_eps [Finite F] (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) : IsSquare (-1 : F) ↔ ε = 1 := by
  have := Fintype.ofFinite F
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
  unfold Int.ModEq at hq
  rcases hε with rfl | rfl <;> omega

theorem card_roots [Finite F] (h2 : (2 : F) ≠ 0) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) :
    (Nat.card {t : F // t ^ 2 + 1 = 0} : ℤ) = 1 + ε := by
  have hiff := isSquare_neg_one_iff_eps (F := F) ε hε hq
  by_cases hsq : IsSquare (-1 : F)
  · have hε1 : ε = 1 := hiff.1 hsq
    obtain ⟨i, hi⟩ := hsq
    have hi0 : i ≠ 0 := by
      rintro rfl
      simp at hi
    have hne : i ≠ -i := by
      intro h
      apply h2
      have : i * 2 = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left hi0
    have hset : {t : F | t ^ 2 + 1 = 0} = {i, -i} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro ht
        have : t ^ 2 = i ^ 2 := by linear_combination ht + hi
        exact sq_eq_sq_iff_eq_or_eq_neg.1 this
      · rintro (rfl | rfl) <;> linear_combination -hi
    have : Nat.card {t : F // t ^ 2 + 1 = 0} = 2 := by
      have h1 : Nat.card {t : F // t ^ 2 + 1 = 0} = ({t : F | t ^ 2 + 1 = 0}).ncard :=
        Nat.card_coe_set_eq _
      rw [h1, hset, Set.ncard_pair hne]
    rw [this, hε1]
    norm_num
  · have hε1 : ε = -1 := by
      rcases hε with h | h
      · exact absurd (hiff.2 h) hsq
      · exact h
    have : IsEmpty {t : F // t ^ 2 + 1 = 0} :=
      ⟨fun ⟨t, ht⟩ => hsq ⟨t, by linear_combination -ht⟩⟩
    rw [Nat.card_of_isEmpty, hε1]
    norm_num

theorem card_conic [Finite F] (h2 : (2 : F) ≠ 0) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) :
    (Nat.card (Conic F) : ℤ) = Nat.card F - ε := by
  have := Fintype.ofFinite F
  classical
  have h1 : Nat.card (Conic F) = Nat.card (Option (Stereo F)) := Nat.card_congr (conicEquiv h2)
  have hs : Fintype.card {t : F // ¬ (t ^ 2 + 1 = 0)} =
      Fintype.card F - Fintype.card {t : F // t ^ 2 + 1 = 0} := Fintype.card_subtype_compl _
  have hle : Fintype.card {t : F // t ^ 2 + 1 = 0} ≤ Fintype.card F := Fintype.card_subtype_le _
  have hr := card_roots h2 ε hε hq
  rw [Nat.card_eq_fintype_card] at hr
  rw [h1, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]
  have hs' : Fintype.card (Stereo F) = Fintype.card F - Fintype.card {t : F // t ^ 2 + 1 = 0} := hs
  rw [hs']
  omega

def so2Equiv : ↥(SO2 F) ≃ Conic F where
  toFun m := ⟨((m : GL (Fin 2) F) 0 0, (m : GL (Fin 2) F) 0 1), ((mem_SO2_iff _).1 m.2).2.2⟩
  invFun p := ⟨rotGL p.1.1 p.1.2 p.2, rotGL_mem _ _ _⟩
  left_inv m := by
    obtain ⟨m, hm⟩ := m
    obtain ⟨h1, h2, h3⟩ := (mem_SO2_iff _).1 hm
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_rotGL, h1, h2]
  right_inv p := rfl

theorem card_SO2 [Finite F] (h2 : (2 : F) ≠ 0) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) :
    (Nat.card ↥(SO2 F) : ℤ) = Nat.card F - ε := by
  rw [Nat.card_congr so2Equiv]
  exact card_conic h2 ε hε hq

end Count

section Cyclic

variable {F : Type} [Field F]

theorem eq_of_add_mul_eq {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {i : K} (hi : -1 = i * i)
    {a b a' b' : K} (nm : a ^ 2 + b ^ 2 = 1) (nn : a' ^ 2 + b' ^ 2 = 1)
    (h : a + b * i = a' + b' * i) : a = a' ∧ b = b' := by
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hzw : (a + b * i) * (a - b * i) = 1 := by linear_combination nm + b ^ 2 * hi
  have hzw' : (a' + b' * i) * (a' - b' * i) = 1 := by linear_combination nn + b' ^ 2 * hi
  have hz0 : a + b * i ≠ 0 := left_ne_zero_of_mul_eq_one hzw
  have hw : a - b * i = a' - b' * i := by
    apply mul_left_cancel₀ hz0
    rw [hzw, h]
    exact hzw'.symm
  have e1 : (2 : K) * a = 2 * a' := by linear_combination h + hw
  have e2 : (2 : K) * (i * b) = 2 * (i * b') := by linear_combination h - hw
  refine ⟨mul_left_cancel₀ h2 e1, ?_⟩
  exact mul_left_cancel₀ hi0 (mul_left_cancel₀ h2 e2)

theorem isCyclic_SO2 [Finite F] (h2 : (2 : F) ≠ 0) : IsCyclic ↥(SO2 F) := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_eq_mul_self (-1 : AlgebraicClosure F)
  have hι : Function.Injective (algebraMap F (AlgebraicClosure F)) :=
    (algebraMap F (AlgebraicClosure F)).injective
  have h2K : (2 : AlgebraicClosure F) ≠ 0 := by
    intro h
    apply h2
    have h' : algebraMap F (AlgebraicClosure F) 2 = algebraMap F _ 0 := by
      rw [map_ofNat, map_zero]; exact h
    exact hι h'
  let φ : ↥(SO2 F) →* AlgebraicClosure F :=
    { toFun := fun m => algebraMap F _ ((m : GL (Fin 2) F) 0 0) +
        algebraMap F _ ((m : GL (Fin 2) F) 0 1) * u
      map_one' := by simp
      map_mul' := by
        rintro ⟨m, hm⟩ ⟨n, hn⟩
        obtain ⟨hn1, hn2, hn3⟩ := (mem_SO2_iff _).1 hn
        show algebraMap F _ ((m * n : GL (Fin 2) F) 0 0) +
          algebraMap F _ ((m * n : GL (Fin 2) F) 0 1) * u =
          (algebraMap F _ ((m : GL (Fin 2) F) 0 0) + algebraMap F _ ((m : GL (Fin 2) F) 0 1) * u) *
          (algebraMap F _ ((n : GL (Fin 2) F) 0 0) + algebraMap F _ ((n : GL (Fin 2) F) 0 1) * u)
        simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hn1, hn2, map_add, map_mul,
          map_neg]
        linear_combination (algebraMap F _ ((m : GL (Fin 2) F) 0 1) *
          algebraMap F _ ((n : GL (Fin 2) F) 0 1)) * hu }
  refine isCyclic_of_injective_ringHom φ ?_
  rintro ⟨m, hm⟩ ⟨n, hn⟩ hmn
  obtain ⟨hm1, hm2, hm3⟩ := (mem_SO2_iff _).1 hm
  obtain ⟨hn1, hn2, hn3⟩ := (mem_SO2_iff _).1 hn
  have nm : (algebraMap F (AlgebraicClosure F) ((m : GL (Fin 2) F) 0 0)) ^ 2 +
      (algebraMap F (AlgebraicClosure F) ((m : GL (Fin 2) F) 0 1)) ^ 2 = 1 := by
    have := congrArg (algebraMap F (AlgebraicClosure F)) hm3
    simpa using this
  have nn : (algebraMap F (AlgebraicClosure F) ((n : GL (Fin 2) F) 0 0)) ^ 2 +
      (algebraMap F (AlgebraicClosure F) ((n : GL (Fin 2) F) 0 1)) ^ 2 = 1 := by
    have := congrArg (algebraMap F (AlgebraicClosure F)) hn3
    simpa using this
  obtain ⟨ha, hb⟩ := eq_of_add_mul_eq h2K hu nm nn hmn
  have ha' := hι ha
  have hb' := hι hb
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases r <;> fin_cases c <;> simp [ha', hb', hm1, hm2, hn1, hn2]

theorem neg_one_mem_SO2 : (-1 : GL (Fin 2) F) ∈ SO2 F := by
  rw [mem_SO2_iff]
  simp


theorem neg_ne_one_GL (h2 : (2 : F) ≠ 0) : (-1 : GL (Fin 2) F) ≠ 1 := by
  intro h
  have := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp at this
  apply h2
  linear_combination -this

theorem exists_generator_SO2 [Finite F] (h2 : (2 : F) ≠ 0) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (m : ℕ) (hm : (m : ℤ) = Nat.card F - ε) :
    ∃ g : GL (Fin 2) F, g ∈ SO2 F ∧ orderOf g = m ∧ ∀ s ∈ SO2 F, ∃ i : ℤ, s = g ^ i := by
  have := isCyclic_SO2 h2
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := ↥(SO2 F))
  refine ⟨γ, γ.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hγ]
    have := card_SO2 h2 ε hε hq
    omega
  · intro s hs
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hγ ⟨s, hs⟩)
    exact ⟨i, by have := congrArg Subtype.val hi; simpa using this.symm⟩

theorem pow_eq_neg_one_of_generator (h2 : (2 : F) ≠ 0) {g : GL (Fin 2) F} {k : ℕ}
    (hord : orderOf g = 2 * k) (hall : ∃ i : ℤ, (-1 : GL (Fin 2) F) = g ^ i) : g ^ k = -1 := by
  obtain ⟨i, hi⟩ := hall
  have hdvd : ((2 * k : ℕ) : ℤ) ∣ 2 * i := by
    rw [← hord, orderOf_dvd_iff_zpow_eq_one, mul_comm, _root_.zpow_mul, ← hi]
    simp
  have hki : (k : ℤ) ∣ i := by
    have : (2 : ℤ) * k ∣ 2 * i := by simpa using hdvd
    exact (mul_dvd_mul_iff_left (two_ne_zero)).1 this
  obtain ⟨t, ht⟩ := hki
  have hgk : (g ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, ← hord]; exact pow_orderOf_eq_one g
  have key : (-1 : GL (Fin 2) F) = (g ^ k) ^ t := by
    rw [hi, ht, _root_.zpow_mul, zpow_natCast]
  rcases Int.even_or_odd' t with ⟨s, rfl | rfl⟩
  · exfalso
    apply neg_ne_one_GL h2
    rw [key, _root_.zpow_mul]
    simp [hgk]
  · rw [key, _root_.zpow_add, _root_.zpow_mul]
    simp [hgk]

theorem mem_zpowers_neg_one_iff (a : GL (Fin 2) F) :
    a ∈ Subgroup.zpowers (-1 : GL (Fin 2) F) ↔ a = 1 ∨ a = -1 := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨t, rfl⟩
    rcases Int.even_or_odd t with h | h
    · exact Or.inl (h.neg_one_zpow)
    · exact Or.inr (h.neg_one_zpow)
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem sig_mul_mul_sig_mul_SO2 {r : GL (Fin 2) F} (hr : r ∈ SO2 F) :
    sig F * r * sig F * r = 1 := by
  rw [sig_mul_mul_sig_mul (SO2_le_Rx hr)]
  have hdet : Matrix.GeneralLinearGroup.det r = 1 := by
    obtain ⟨h1, h2, h3⟩ := (mem_SO2_iff _).1 hr
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h1, h2]
    simp only [Units.val_one]
    linear_combination h3
  rw [hdet, map_one]

end Cyclic

section Hilbert

variable {F : Type} [Field F]

theorem Rx_comm {r s : GL (Fin 2) F} (hr : r ∈ Rx F) (hs : s ∈ Rx F) : r * s = s * r := by
  obtain ⟨a, b, hab⟩ := exists_eq_of_mem_Rx hr
  obtain ⟨c, d, hcd⟩ := exists_eq_of_mem_Rx hs
  apply Units.ext
  simp only [Units.val_mul, hab, hcd]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring


theorem jm_mem_Rx : jm F ∈ Rx F := by
  rw [Rx, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]

noncomputable def theta (F : Type) [Field F] : ↥(Rx F) →* GL (Fin 2) F where
  toFun r := Matrix.GeneralLinearGroup.scalar (Fin 2)
    (Matrix.GeneralLinearGroup.det (r : GL (Fin 2) F))⁻¹ * (r : GL (Fin 2) F) ^ 2
  map_one' := by simp
  map_mul' := by
    intro r s
    have hc : Commute (r : GL (Fin 2) F) (s : GL (Fin 2) F) := Rx_comm r.2 s.2
    simp only [Subgroup.coe_mul, map_mul, mul_inv]
    rw [hc.mul_pow]
    have hBX : Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Matrix.GeneralLinearGroup.det (s : GL (Fin 2) F))⁻¹ * (r : GL (Fin 2) F) ^ 2 =
        (r : GL (Fin 2) F) ^ 2 * Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Matrix.GeneralLinearGroup.det (s : GL (Fin 2) F))⁻¹ :=
      Matrix.GeneralLinearGroup.scalar_commute _ _
    simp only [mul_assoc]
    rw [← mul_assoc ((r : GL (Fin 2) F) ^ 2), ← hBX]
    simp only [mul_assoc]

theorem coe_theta (r : ↥(Rx F)) {a b : F}
    (hab : ((r : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![a, b; -b, a]) :
    ((theta F r : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2), 2 * a * b / (a ^ 2 + b ^ 2);
         -(2 * a * b / (a ^ 2 + b ^ 2)), (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2)] := by
  show (((Matrix.GeneralLinearGroup.scalar (Fin 2)
    (Matrix.GeneralLinearGroup.det (r : GL (Fin 2) F))⁻¹ * (r : GL (Fin 2) F) ^ 2 : GL (Fin 2) F)) :
    Matrix (Fin 2) (Fin 2) F) = _
  have hdet : ((Matrix.GeneralLinearGroup.det (r : GL (Fin 2) F) : Fˣ) : F) = a ^ 2 + b ^ 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hab, Matrix.det_fin_two_of]; ring
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, hab,
    Units.val_inv_eq_inv_val, hdet]
  ext c d
  fin_cases c <;> fin_cases d <;> simp [pow_two, Matrix.mul_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply] <;> ring

theorem norm_ne_zero_of_mem_Rx {r : GL (Fin 2) F} {a b : F}
    (hab : (r : Matrix (Fin 2) (Fin 2) F) = !![a, b; -b, a]) : a ^ 2 + b ^ 2 ≠ 0 := by
  have := Matrix.GeneralLinearGroup.det_ne_zero r
  rw [hab, Matrix.det_fin_two_of] at this
  intro h
  apply this
  linear_combination h


theorem theta_eq_one_iff (h2 : (2 : F) ≠ 0) (r : ↥(Rx F)) :
    theta F r = 1 ↔ ∃ c : Fˣ, (r : GL (Fin 2) F) = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  obtain ⟨a, b, hab⟩ := exists_eq_of_mem_Rx r.2
  have hN := norm_ne_zero_of_mem_Rx hab
  constructor
  · intro h
    have hc := coe_theta r hab
    rw [h, Units.val_one] at hc
    have e00 := congrFun₂ hc 0 0
    simp at e00
    have hb : b = 0 := by
      field_simp at e00
      have : (2 : F) * b ^ 2 = 0 := by linear_combination e00
      have := (mul_eq_zero.1 this).resolve_left h2
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have ha : a ≠ 0 := by
      intro ha
      apply hN
      rw [ha, hb]
      ring
    refine ⟨Units.mk0 a ha, ?_⟩
    apply Units.ext
    rw [hab, hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  · rintro ⟨c, hc⟩
    have hrc : ((r : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(c : F), 0; -0, (c : F)] := by
      rw [hc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
    have h := coe_theta r hrc
    have hc0 : (c : F) ^ 2 + 0 ^ 2 ≠ 0 := by simp
    apply Units.ext
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem theta_surjective (h2 : (2 : F) ≠ 0) {s : GL (Fin 2) F} (hs : s ∈ SO2 F) :
    ∃ r : ↥(Rx F), theta F r = s := by
  obtain ⟨a, b, hab⟩ := exists_eq_of_mem_Rx (SO2_le_Rx hs)
  have hnorm : a ^ 2 + b ^ 2 = 1 := by
    have h3 := ((mem_SO2_iff _).1 hs).2.2
    rw [hab] at h3
    simpa using h3
  by_cases ha : a = -1
  · have hb : b = 0 := by
      have : b ^ 2 = 0 := by rw [ha] at hnorm; linear_combination hnorm
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    refine ⟨⟨jm F, jm_mem_Rx⟩, ?_⟩
    have h := coe_theta (⟨jm F, jm_mem_Rx⟩ : ↥(Rx F)) (a := 0) (b := 1) (by
      show ((jm F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
      rw [coe_jm])
    apply Units.ext
    rw [h, hab, ha, hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have hden : (1 + a) ≠ 0 := fun h => ha (by linear_combination h)
    have hdet : (1 + a) ^ 2 + b ^ 2 = 2 * (1 + a) := by linear_combination hnorm
    have hdet' : (1 + a) * (1 + a) - b * (-b) ≠ 0 := by
      have : (1 + a) * (1 + a) - b * (-b) = 2 * (1 + a) := by linear_combination hnorm
      rw [this]
      exact mul_ne_zero h2 hden
    let r₀ : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1 + a, b; -b, 1 + a]
      (by rw [Matrix.det_fin_two_of]; exact hdet')
    have hr₀ : (r₀ : Matrix (Fin 2) (Fin 2) F) = !![1 + a, b; -b, 1 + a] := rfl
    have hrx : r₀ ∈ Rx F := (mem_Rx_iff _).2 ⟨by simp [hr₀], by simp [hr₀]⟩
    refine ⟨⟨r₀, hrx⟩, ?_⟩
    have h := coe_theta (⟨r₀, hrx⟩ : ↥(Rx F)) (a := 1 + a) (b := b) hr₀
    apply Units.ext
    rw [h, hab, hdet]
    have e1 : ((1 + a) ^ 2 - b ^ 2) / (2 * (1 + a)) = a := by
      rw [div_eq_iff (mul_ne_zero h2 hden)]
      linear_combination (-1 : F) * hnorm
    have e2 : 2 * (1 + a) * b / (2 * (1 + a)) = b := by
      field_simp
    rw [e1, e2]


end Hilbert

end O2Plane


end CFSG.GH74.GLS.IVK.Proofs2.Sp48
