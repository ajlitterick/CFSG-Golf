module

public import CFSG.Monster.Xi.Defs
public import CFSG.Monster.Xi.GreyIdentities
public import CFSG.Monster.Spin.DyadicNormalizer
import CFSG.Monster.FourierTriality
public import CFSG.Monster.Spin.FourierPauli

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Xi

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem add_self_fin6 (μ : Fin 6 → ZMod 2) : μ + μ = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact zmod2_add_self _

private theorem add_add_cancel_fin6 (μ κ : Fin 6 → ZMod 2) : μ + (μ + κ) = κ := by
  rw [← add_assoc, add_self_fin6, zero_add]

private theorem add_add_cancel_fin6' (ν μ : Fin 6 → ZMod 2) : ν + μ + μ = ν := by
  rw [add_assoc, add_self_fin6, add_zero]

private theorem sum_add_right' {M : Type*} [AddCommMonoid M] (f : (Fin 6 → ZMod 2) → M)
    (μ : Fin 6 → ZMod 2) : ∑ ν, f (ν + μ) = ∑ ν, f ν :=
  Equiv.sum_comp (Equiv.addRight μ) f

private theorem sum_add_left' {M : Type*} [AddCommMonoid M] (f : (Fin 6 → ZMod 2) → M)
    (μ : Fin 6 → ZMod 2) : ∑ ν, f (μ + ν) = ∑ ν, f ν :=
  Equiv.sum_comp (Equiv.addLeft μ) f

theorem zmat_pow_val (t : ZMod 2) : zmat ^ t.val = sgn t • (1 : Matrix SpinIdx SpinIdx ℚ) := by
  have : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases this t with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, sgn_zero, one_smul]
  · rw [ZMod.val_one, pow_one, zmat, show sgn 1 = -1 from rfl, neg_one_smul]

theorem Dmat_mul_Tmat_eq (δ : Cocode) (a : C) :
    Dmat δ * Tmat a = sgn (pair a δ) • (Tmat a * Dmat δ) := by
  rw [Dmat_mul_Tmat, zmat_pow_val, Matrix.smul_mul, Matrix.one_mul]

@[simp] theorem Tmat_zero : Tmat 0 = 1 := by
  rw [Tmat_eq_qmatR, qmatR_zero]

@[simp] theorem Dmat_zero : Dmat 0 = 1 := by
  rw [Dmat_eq_qmatR, qmatR_zero]

theorem Tmat_comm (a b : C) : Tmat a * Tmat b = Tmat b * Tmat a := by
  rw [Tmat_mul_Tmat, Tmat_mul_Tmat, add_comm]

theorem Dmat_comm (δ ε : Cocode) : Dmat δ * Dmat ε = Dmat ε * Dmat δ := by
  rw [Dmat_mul_Dmat, Dmat_mul_Dmat, add_comm]

theorem Tmat_mul_self (a : C) : Tmat a * Tmat a = 1 := by
  rw [Tmat_mul_Tmat, add_self_C', Tmat_zero]


theorem Tmat_transpose (a : C) : (Tmat a)ᵀ = Tmat a := by
  rw [Tmat_eq_qmatR, qmatR_transpose, pair_zero_right, add_zero]

theorem Dmat_transpose (δ : Cocode) : (Dmat δ)ᵀ = Dmat δ := by
  rw [Dmat_eq_qmatR, qmatR_transpose, pair_zero_left, add_zero]

theorem Dg_mul_Tg (μ ν : Fin 6 → ZMod 2) :
    Dmat (gammaD ν) * Tmat (greyC μ) = sgn (bG μ ν) • (Tmat (greyC μ) * Dmat (gammaD ν)) := by
  rw [Dmat_mul_Tmat_eq, pair_greyC_gammaD]

theorem Dg_mul_TH (ν : Fin 6 → ZMod 2) {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) :
    Dmat (gammaD ν) * Tmat h = Tmat h * Dmat (gammaD ν) := by
  rw [Dmat_mul_Tmat_eq, pair_H_gammaD hh, sgn_zero, one_smul]

theorem DHstar_mul_Tg {η : Cocode} (hη : η ∈ Hstar) (μ : Fin 6 → ZMod 2) :
    Dmat η * Tmat (greyC μ) = Tmat (greyC μ) * Dmat η := by
  rw [Dmat_mul_Tmat_eq, mem_Hstar_iff.1 hη μ, sgn_zero, one_smul]

private theorem sum_sgn_qG_mul_aux : ∀ κ : Fin 6 → ZMod 2,
    ∑ ν : Fin 6 → ZMod 2, sgn (qG ν) * sgn (qG (ν + κ)) = if κ = 0 then 64 else 0 := by
  decide +kernel

theorem sum_sgn_qG_mul (κ : Fin 6 → ZMod 2) :
    ∑ ν : Fin 6 → ZMod 2, sgn (qG ν) * sgn (qG (ν + κ)) = if κ = 0 then 64 else 0 :=
  sum_sgn_qG_mul_aux κ

theorem sum_sum_sgn_qG {V : Type*} [AddCommGroup V] [Module ℚ V]
    (X : (Fin 6 → ZMod 2) → V) :
    ∑ μ : Fin 6 → ZMod 2, ∑ ν : Fin 6 → ZMod 2, (sgn (qG μ) * sgn (qG ν)) • X (μ + ν) =
      (64 : ℚ) • X 0 := by
  have h1 : ∀ μ : Fin 6 → ZMod 2, ∑ ν : Fin 6 → ZMod 2, (sgn (qG μ) * sgn (qG ν)) • X (μ + ν) =
      ∑ κ : Fin 6 → ZMod 2, (sgn (qG μ) * sgn (qG (μ + κ))) • X κ := by
    intro μ
    rw [← sum_add_left' (fun ν => (sgn (qG μ) * sgn (qG ν)) • X (μ + ν)) μ]
    simp only [add_add_cancel_fin6]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, sum_sgn_qG_mul, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem XiGamma_transpose : XiGammaᵀ = XiGamma := by
  rw [XiGamma, transpose_smul, transpose_sum]
  simp only [transpose_smul, Dmat_transpose]

theorem XiG_transpose : XiGᵀ = XiG := by
  rw [XiG, transpose_smul, transpose_sum]
  simp only [transpose_smul, Tmat_transpose]

private theorem avg_mul_avg (F F' : (Fin 6 → ZMod 2) → Matrix SpinIdx SpinIdx ℚ) :
    ((1 / 8 : ℚ) • ∑ μ : Fin 6 → ZMod 2, sgn (qG μ) • F μ) *
        ((1 / 8 : ℚ) • ∑ ν : Fin 6 → ZMod 2, sgn (qG ν) • F' ν) =
      (1 / 64 : ℚ) • ∑ μ : Fin 6 → ZMod 2, ∑ ν : Fin 6 → ZMod 2,
        (sgn (qG μ) * sgn (qG ν)) • (F μ * F' ν) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul]
  simp only [Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num [mul_comm]

theorem XiGamma_mul_self : XiGamma * XiGamma = 1 := by
  rw [XiGamma, avg_mul_avg]
  simp only [Dmat_mul_Dmat, ← map_add]
  rw [sum_sum_sgn_qG (fun κ => Dmat (gammaD κ)), map_zero, Dmat_zero, smul_smul]
  norm_num

theorem XiG_mul_self : XiG * XiG = 1 := by
  rw [XiG, avg_mul_avg]
  simp only [Tmat_mul_Tmat, ← map_add]
  rw [sum_sum_sgn_qG (fun κ => Tmat (greyC κ)), map_zero, Tmat_zero, smul_smul]
  norm_num


theorem Tg_mul_XiGamma (μ : Fin 6 → ZMod 2) :
    Tmat (greyC μ) * XiGamma =
      XiGamma * (sgn (qG μ) • (Tmat (greyC μ) * Dmat (gammaD μ))) := by
  have hL : ∀ ν : Fin 6 → ZMod 2, Tmat (greyC μ) * (sgn (qG ν) • Dmat (gammaD ν)) =
      sgn (qG ν) • (Tmat (greyC μ) * Dmat (gammaD ν)) := fun ν => Matrix.mul_smul _ _ _
  have hR : ∀ ν : Fin 6 → ZMod 2, sgn (qG ν) • Dmat (gammaD ν) *
      (sgn (qG μ) • (Tmat (greyC μ) * Dmat (gammaD μ))) =
      sgn (qG (ν + μ)) • (Tmat (greyC μ) * Dmat (gammaD (ν + μ))) := by
    intro ν
    have hc : sgn (qG ν) * sgn (qG μ) * sgn (bG μ ν) = sgn (qG (ν + μ)) := by
      rw [← sgn_add, ← sgn_add, qG_add, bG_comm ν μ]
    rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Dg_mul_Tg, Matrix.smul_mul,
      Matrix.mul_assoc, Dmat_mul_Dmat, ← map_add, smul_smul, smul_smul, hc]
  rw [XiGamma, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  refine congrArg ((1 / 8 : ℚ) • ·) ?_
  simp only [hL, hR]
  exact (sum_add_right' (fun ν => sgn (qG ν) • (Tmat (greyC μ) * Dmat (gammaD ν))) μ).symm

theorem Dg_mul_XiG (ν : Fin 6 → ZMod 2) :
    Dmat (gammaD ν) * XiG = XiG * (sgn (qG ν) • (Tmat (greyC ν) * Dmat (gammaD ν))) := by
  have hL : ∀ μ : Fin 6 → ZMod 2, Dmat (gammaD ν) * (sgn (qG μ) • Tmat (greyC μ)) =
      (sgn (qG μ) * sgn (bG μ ν)) • (Tmat (greyC μ) * Dmat (gammaD ν)) := by
    intro μ
    rw [Matrix.mul_smul, Dg_mul_Tg, smul_smul]
  have hR : ∀ μ : Fin 6 → ZMod 2, sgn (qG μ) • Tmat (greyC μ) *
      (sgn (qG ν) • (Tmat (greyC ν) * Dmat (gammaD ν))) =
      (sgn (qG μ) * sgn (qG ν)) • (Tmat (greyC (μ + ν)) * Dmat (gammaD ν)) := by
    intro μ
    rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Tmat_mul_Tmat, ← map_add,
      smul_smul]
  rw [XiG, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  refine congrArg ((1 / 8 : ℚ) • ·) ?_
  simp only [hL, hR]
  rw [← sum_add_right' (fun μ => (sgn (qG μ) * sgn (qG ν)) •
    (Tmat (greyC (μ + ν)) * Dmat (gammaD ν))) ν]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [add_add_cancel_fin6']
  have hc : sgn (qG (μ + ν)) * sgn (qG ν) = sgn (qG μ) * sgn (bG μ ν) := by
    rw [← sgn_add, ← sgn_add, qG_add]
    congr 1
    linear_combination qG ν * two_eq_zero'
  rw [hc]

theorem Dmat_mul_XiGamma (δ : Cocode) : Dmat δ * XiGamma = XiGamma * Dmat δ := by
  rw [XiGamma, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Dmat_comm δ]

theorem Tmat_mul_XiG (a : C) : Tmat a * XiG = XiG * Tmat a := by
  rw [XiG, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Tmat_comm a]

theorem TH_mul_XiGamma {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) :
    Tmat h * XiGamma = XiGamma * Tmat h := by
  rw [XiGamma, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Dg_mul_TH _ hh]

theorem DHstar_mul_XiG {η : Cocode} (hη : η ∈ Hstar) : Dmat η * XiG = XiG * Dmat η := by
  rw [XiG, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, DHstar_mul_Tg hη]

@[expose] def XiW : Matrix SpinIdx SpinIdx ℚ :=
  (1 / 8 : ℚ) • ∑ μ : Fin 6 → ZMod 2, Tmat (greyC μ) * Dmat (gammaD μ)

theorem XiG_mul_XiGamma : XiG * XiGamma = XiGamma * XiW := by
  rw [XiG, Matrix.smul_mul, Finset.sum_mul, XiW, Matrix.mul_smul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Matrix.smul_mul, Tg_mul_XiGamma, Matrix.mul_smul, smul_smul, sgn_mul_self, one_smul]

theorem XiGamma_mul_XiG : XiGamma * XiG = XiG * XiW := by
  rw [XiGamma, Matrix.smul_mul, Finset.sum_mul, XiW, Matrix.mul_smul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Matrix.smul_mul, Dg_mul_XiG, Matrix.mul_smul, smul_smul, sgn_mul_self, one_smul]

theorem XiGamma_XiG_XiGamma : XiGamma * XiG * XiGamma = XiW := by
  rw [Matrix.mul_assoc, XiG_mul_XiGamma, ← Matrix.mul_assoc, XiGamma_mul_self, Matrix.one_mul]

theorem XiG_XiGamma_XiG : XiG * XiGamma * XiG = XiW := by
  rw [Matrix.mul_assoc, XiGamma_mul_XiG, ← Matrix.mul_assoc, XiG_mul_self, Matrix.one_mul]

theorem Ximat_pow_three : Ximat ^ 3 = 1 := by
  have hW : XiW * XiW = 1 := by
    calc XiW * XiW = XiGamma * XiG * (XiGamma * XiGamma) * XiG * XiGamma := by
          rw [← XiGamma_XiG_XiGamma]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [XiGamma_mul_self, Matrix.mul_one, Matrix.mul_assoc XiGamma, XiG_mul_self,
            Matrix.mul_one, XiGamma_mul_self]
  calc Ximat ^ 3 = (XiGamma * XiG * XiGamma) * (XiG * XiGamma * XiG) := by
        rw [pow_succ, pow_two, Ximat]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [XiGamma_XiG_XiGamma, XiG_XiGamma_XiG, hW]

theorem Ximat_transpose : Ximatᵀ = XiG * XiGamma := by
  rw [Ximat, transpose_mul, XiGamma_transpose, XiG_transpose]

theorem Ximat_transpose_mul_self : Ximatᵀ * Ximat = 1 := by
  rw [Ximat_transpose, Ximat, Matrix.mul_assoc, ← Matrix.mul_assoc XiGamma, XiGamma_mul_self,
    Matrix.one_mul, XiG_mul_self]

theorem Ximat_mul_transpose_self : Ximat * Ximatᵀ = 1 := by
  rw [Ximat_transpose, Ximat, Matrix.mul_assoc, ← Matrix.mul_assoc XiG, XiG_mul_self,
    Matrix.one_mul, XiGamma_mul_self]

theorem Ximat_inv : Ximat⁻¹ = Ximatᵀ := Matrix.inv_eq_left_inv Ximat_transpose_mul_self

theorem Ximat_inv_mul_self : Ximat⁻¹ * Ximat = 1 := by
  rw [Ximat_inv, Ximat_transpose_mul_self]


theorem conj_eq_of_mul_eq {X Y : Matrix SpinIdx SpinIdx ℚ} (h : X * Ximat = Ximat * Y) :
    Ximat⁻¹ * X * Ximat = Y := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Ximat_inv_mul_self, Matrix.one_mul]


theorem Tg_mul_Ximat (μ : Fin 6 → ZMod 2) :
    Tmat (greyC μ) * Ximat = Ximat * Dmat (gammaD μ) := by
  rw [Ximat, ← Matrix.mul_assoc, Tg_mul_XiGamma, Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  rw [Matrix.smul_mul, Matrix.mul_assoc, Dg_mul_XiG, ← Matrix.mul_assoc, Tmat_mul_XiG,
    Matrix.mul_assoc, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc (Tmat _),
    Tmat_mul_self, Matrix.one_mul, smul_smul, sgn_mul_self, one_smul]

theorem Dg_mul_Ximat (ν : Fin 6 → ZMod 2) :
    Dmat (gammaD ν) * Ximat = Ximat * (sgn (qG ν) • (Tmat (greyC ν) * Dmat (gammaD ν))) := by
  rw [Ximat, ← Matrix.mul_assoc, Dmat_mul_XiGamma, Matrix.mul_assoc, Dg_mul_XiG,
    Matrix.mul_assoc]

theorem TH_mul_Ximat {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) :
    Tmat h * Ximat = Ximat * Tmat h := by
  rw [Ximat, ← Matrix.mul_assoc, TH_mul_XiGamma hh, Matrix.mul_assoc, Tmat_mul_XiG,
    Matrix.mul_assoc]

theorem DHstar_mul_Ximat {η : Cocode} (hη : η ∈ Hstar) : Dmat η * Ximat = Ximat * Dmat η := by
  rw [Ximat, ← Matrix.mul_assoc, Dmat_mul_XiGamma, Matrix.mul_assoc, DHstar_mul_XiG hη,
    Matrix.mul_assoc]


theorem conj_Ximat (μ ν : Fin 6 → ZMod 2) {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) {η : Cocode}
    (hη : η ∈ Hstar) :
    Ximat⁻¹ * (Tmat (greyC μ) * Tmat h * Dmat (gammaD ν) * Dmat η) * Ximat =
      sgn (qG ν + bG μ ν) • (Tmat (greyC ν) * Tmat h * Dmat (gammaD (μ + ν)) * Dmat η) := by
  apply conj_eq_of_mul_eq
  have e1 : Tmat (greyC μ) * Tmat h * Dmat (gammaD ν) * Dmat η * Ximat =
      Ximat * (Dmat (gammaD μ) * Tmat h * (sgn (qG ν) • (Tmat (greyC ν) * Dmat (gammaD ν))) *
        Dmat η) := by
    simp only [Matrix.mul_assoc]
    rw [DHstar_mul_Ximat hη, ← Matrix.mul_assoc (Dmat (gammaD ν)), Dg_mul_Ximat,
      Matrix.mul_assoc, ← Matrix.mul_assoc (Tmat h), TH_mul_Ximat hh, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Tmat (greyC μ)), Tg_mul_Ximat]
    simp only [Matrix.mul_assoc]
  rw [e1]
  refine congrArg (Ximat * ·) ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, Dg_mul_TH μ hh, Matrix.mul_assoc (Tmat h),
    ← Matrix.mul_assoc (Dmat (gammaD μ)), Dg_mul_Tg, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, ← sgn_add, Matrix.mul_assoc (Tmat (greyC ν)),
    Dmat_mul_Dmat, ← map_add, bG_comm ν μ, ← Matrix.mul_assoc (Tmat h), Tmat_comm h]

theorem qmatR_mem_Qmats (s : ZMod 2) (a : C) (δ : Cocode) : qmatR ℚ s a δ ∈ Qmats :=
  ⟨toGL ⟨s, a, δ⟩, by rw [← range_toGL]; exact ⟨_, rfl⟩, coe_toGL _⟩

theorem mem_Qmats_iff {g : Matrix SpinIdx SpinIdx ℚ} :
    g ∈ Qmats ↔ ∃ (s : ZMod 2) (a : C) (δ : Cocode), g = qmatR ℚ s a δ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [← range_toGL] at hu
    obtain ⟨x, rfl⟩ := hu
    exact ⟨x.s, x.a, x.δ, coe_toGL x⟩
  · rintro ⟨s, a, δ, rfl⟩
    exact qmatR_mem_Qmats s a δ

theorem exists_greyC_add (a : C) :
    ∃ (μ : Fin 6 → ZMod 2) (h : C), (h : Fin 24 → ZMod 2) ∈ H ∧ a = greyC μ + h := by
  have ha : (a : Fin 24 → ZMod 2) ∈ G ⊔ H := by rw [G_sup_H]; exact a.2
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 ha
  obtain ⟨μ, hμ⟩ := (mem_G_iff x).1 hx
  refine ⟨μ, ⟨y, H_le_C hy⟩, hy, Subtype.ext ?_⟩
  rw [Submodule.coe_add, hμ, ← hxy]

theorem conj_mem_Qmats {g : Matrix SpinIdx SpinIdx ℚ} (hg : g ∈ Qmats) :
    Ximat⁻¹ * g * Ximat ∈ Qmats := by
  obtain ⟨s, a, δ, rfl⟩ := mem_Qmats_iff.1 hg
  obtain ⟨μ, h, hh, rfl⟩ := exists_greyC_add a
  obtain ⟨ν, hν⟩ := exists_gammaD_add_mem_Hstar δ
  set η := δ - gammaD ν
  have hδ : δ = gammaD ν + η := by simp [η]
  rw [hδ, qmatR_eq, ← Tmat_eq, ← Dmat_eq, sgnR_rat, ← Tmat_mul_Tmat, ← Dmat_mul_Dmat,
    Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc (Tmat (greyC μ) * Tmat h),
    conj_Ximat μ ν hh hν, smul_smul, ← sgn_add, Matrix.mul_assoc (Tmat (greyC ν) * Tmat h),
    Tmat_mul_Tmat, Dmat_mul_Dmat, ← sgnR_rat, Tmat_eq, Dmat_eq, ← qmatR_eq]
  exact qmatR_mem_Qmats _ _ _


@[expose] def XiU : GL SpinIdx ℚ :=
  ⟨Ximat, Ximatᵀ, Ximat_mul_transpose_self, Ximat_transpose_mul_self⟩

@[simp] theorem coe_XiU : (XiU : Matrix SpinIdx SpinIdx ℚ) = Ximat := rfl

theorem coe_XiU_inv : ((XiU⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = Ximat⁻¹ := by
  rw [Ximat_inv]
  rfl

theorem mem_Q_iff_coe_mem_Qmats (u : GL SpinIdx ℚ) :
    u ∈ Q ↔ (u : Matrix SpinIdx SpinIdx ℚ) ∈ Qmats := by
  refine ⟨fun hu => ⟨u, hu, rfl⟩, ?_⟩
  rintro ⟨v, hv, hvu⟩
  rwa [← Units.ext hvu]

theorem XiU_inv_conj_mem_Q {u : GL SpinIdx ℚ} (hu : u ∈ Q) : XiU⁻¹ * u * XiU ∈ Q := by
  rw [mem_Q_iff_coe_mem_Qmats, Units.val_mul, Units.val_mul, coe_XiU_inv, coe_XiU]
  exact conj_mem_Qmats ((mem_Q_iff_coe_mem_Qmats u).1 hu)

theorem XiU_mem_normalizer : XiU ∈ Subgroup.normalizer (Q : Set (GL SpinIdx ℚ)) := by
  have h3 : XiU ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, coe_XiU, Ximat_pow_three,
    Units.val_one])
  have hinv : XiU⁻¹ ∈ Subgroup.normalizer (Q : Set (GL SpinIdx ℚ)) := by
    rw [Subgroup.mem_normalizer_iff, inv_inv]
    intro u
    refine ⟨XiU_inv_conj_mem_Q, fun hu => ?_⟩
    have h := XiU_inv_conj_mem_Q (XiU_inv_conj_mem_Q hu)
    have h3' : XiU * XiU * XiU = 1 := by rw [← pow_three', h3]
    have hi : XiU⁻¹ = XiU * XiU := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, h3']
    have e : XiU⁻¹ * (XiU⁻¹ * (XiU⁻¹ * u * XiU) * XiU) * XiU = u := by
      rw [hi]
      simp only [← mul_assoc]
      rw [h3', one_mul, h3', one_mul, mul_assoc u, mul_assoc u, h3', mul_one]
    rwa [e] at h
  have h := Subgroup.inv_mem _ hinv
  rwa [inv_inv] at h


end CFSG.Monster.Xi
