module

public import CFSG.Assembly.Defs
public import CFSG.LieType.Chevalley.RankOneGaussian

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.LieType.Chevalley Matrix Polynomial
open scoped MatrixGroups

section Antidiag

variable {F : Type} [Field F]

theorem conj_vSL_step (τ : F) (p q r : F) :
    ((vSL τ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * !![p, q; r, -p] *
      ((((vSL τ)⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) =
      !![p - τ * q, q; r + 2 * τ * p - τ ^ 2 * q, -(p - τ * q)] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_vSL, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem conj_uSL_step (σ : F) (p q r : F) :
    ((uSL σ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * !![p, q; r, -p] *
      ((((uSL σ)⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) =
      !![p + σ * r, q - 2 * σ * p - σ ^ 2 * r; r, -(p + σ * r)] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_uSL, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem exists_antidiag_conj (h2 : (2 : F) ≠ 0) (M : Matrix (Fin 2) (Fin 2) F) {l : F}
    (hM : M * M = l • 1) (hl : l ≠ 0) (hns : ∀ c : F, M ≠ c • 1) :
    ∃ (R : SL2 F) (b c : F), b ≠ 0 ∧ c ≠ 0 ∧
      (R : Matrix (Fin 2) (Fin 2) F) * M * ((R⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
        !![0, b; c, 0] := by
  have hM' := Matrix.eta_fin_two M
  set p := M 0 0 with hp
  set q := M 0 1 with hq
  set r := M 1 0 with hr
  set s := M 1 1 with hs
  have e00 : p * p + q * r = l := by
    have := congrFun (congrFun hM 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hp, hq, hr, hs] using this
  have e11 : r * q + s * s = l := by
    have := congrFun (congrFun hM 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hp, hq, hr, hs] using this
  have e01 : q * (p + s) = 0 := by
    have := congrFun (congrFun hM 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have e10 : r * (p + s) = 0 := by
    have := congrFun (congrFun hM 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have htr : s = -p := by
    by_contra hne
    have hps : p + s ≠ 0 := fun h => hne (by linear_combination h)
    have hq0 : q = 0 := (mul_eq_zero.mp e01).resolve_right hps
    have hr0 : r = 0 := (mul_eq_zero.mp e10).resolve_right hps
    have hpp : p * p = s * s := by
      rw [hq0] at e00; rw [hr0] at e11; linear_combination e00 - e11
    have hps2 : (p - s) * (p + s) = 0 := by linear_combination hpp
    have hpe : p = s := by
      have := (mul_eq_zero.mp hps2).resolve_right hps
      linear_combination this
    apply hns p
    rw [hM']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hq0, hr0, hpe]
  rw [htr] at hM'
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hex : ∃ τ : F, r + 2 * τ * p - τ ^ 2 * q ≠ 0 := by
    by_contra hall
    have hall' : ∀ τ : F, r + 2 * τ * p - τ ^ 2 * q = 0 := fun τ =>
      not_not.mp (not_exists.mp hall τ)
    have h0 := hall' 0
    have h1 := hall' 1
    have h1' := hall' (-1)
    have hr0 : r = 0 := by simpa using h0
    have hp0 : p = 0 := by
      have : 4 * p = 0 := by
        rw [hr0] at h1 h1'
        linear_combination (h1 - h1')
      exact (mul_eq_zero.mp this).resolve_left h4
    have hq0 : q = 0 := by
      rw [hr0, hp0] at h1; linear_combination -h1
    apply hl
    rw [← e00, hp0, hq0]; ring
  obtain ⟨τ, hτ⟩ := hex
  set r₁ := r + 2 * τ * p - τ ^ 2 * q with hr₁
  set p₁ := p - τ * q with hp₁
  have hstep1 : ((vSL τ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * M *
      ((((vSL τ)⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) = !![p₁, q; r₁, -p₁] := by
    rw [hM', conj_vSL_step]
  have hdet : p₁ * p₁ + q * r₁ = l := by
    rw [hp₁, hr₁, ← e00]; ring
  refine ⟨uSL (-p₁ / r₁) * vSL τ, q + p₁ ^ 2 / r₁, r₁, ?_, hτ, ?_⟩
  · have : q + p₁ ^ 2 / r₁ = l / r₁ := by
      field_simp; linear_combination hdet
    rw [this]; exact div_ne_zero hl hτ
  · have hmul : (((uSL (-p₁ / r₁) * vSL τ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) * M *
        ((((uSL (-p₁ / r₁) * vSL τ)⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) =
        ((uSL (-p₁ / r₁) : SL2 F) : Matrix (Fin 2) (Fin 2) F) *
          (((vSL τ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * M *
            ((((vSL τ)⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F)) *
          ((((uSL (-p₁ / r₁))⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) := by
      rw [_root_.mul_inv_rev]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
    rw [hmul, hstep1, conj_uSL_step]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

end Antidiag

section Conic

variable {F : Type} [Field F]

theorem exists_eval_ne_zero_fin [Finite F] (f : F[X]) (hf : f ≠ 0)
    (hd : f.natDegree < Nat.card F) : ∃ m : F, f.eval m ≠ 0 := by
  have := Fintype.ofFinite F
  exact Polynomial.exists_eval_ne_zero_of_natDegree_lt_card f hf (by
    simpa [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card] using hd)

theorem conic_point (κ m : F) (h : 1 - κ * m ^ 2 ≠ 0) :
    ((1 + κ * m ^ 2) / (1 - κ * m ^ 2)) ^ 2 - κ * (2 * m / (1 - κ * m ^ 2)) ^ 2 = 1 := by
  field_simp
  ring


end Conic

section Torus

variable {F : Type} [Field F]

@[expose] def normTorusSL (κ : F) (s : Fˣ) (u v : F) (h : u ^ 2 - κ * v ^ 2 = 1) : SL2 F :=
  ⟨!![u, (s : F) * v; ((s⁻¹ : Fˣ) : F) * κ * v, u], by
    rw [det_fin_two]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
    have hs : (s : F) * ((s⁻¹ : Fˣ) : F) = 1 := by simp
    linear_combination h - κ * v ^ 2 * hs⟩

theorem coe_normTorusSL (κ : F) (s : Fˣ) (u v : F) (h : u ^ 2 - κ * v ^ 2 = 1) :
    ((normTorusSL κ s u v h : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![u, (s : F) * v; ((s⁻¹ : Fˣ) : F) * κ * v, u] := rfl

theorem uSL_mul_uSL_tt (a b : F) : uSL a * uSL b = uSL (a + b) := by
  apply SL2_ext <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, Matrix.mul_apply,
    Fin.sum_univ_two, add_comm]

theorem uSL_inv_tt (a : F) : (uSL a)⁻¹ = uSL (-a) := by
  rw [inv_eq_iff_mul_eq_one, uSL_mul_uSL_tt, add_neg_cancel]
  apply SL2_ext <;> simp [coe_uSL]

theorem uSL_zero_tt : (uSL (0 : F) : SL2 F) = 1 := by
  apply SL2_ext <;> simp [coe_uSL]

theorem uSL_sub_tt (a b : F) : uSL (a - b) = uSL a * (uSL b)⁻¹ := by
  rw [uSL_inv_tt, uSL_mul_uSL_tt, sub_eq_add_neg]

theorem HSL_conj_uSL_tt (t : Fˣ) (c : F) :
    HSL t * uSL c * (HSL t)⁻¹ = uSL ((t : F) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply SL2_ext <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_HSL, Matrix.mul_apply,
    Fin.sum_univ_two]
  field_simp


end Torus

end CFSG.ClassicalInvolution.G2D4Models
