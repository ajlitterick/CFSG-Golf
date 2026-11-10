module

public import CFSG.Quasithin.Vol2.Ch3E213MP6BL
public import CFSG.Quasithin.Vol2.Ch3E213MP6BH

public section

namespace CFSG.Quasithin.Ch3E213M.P6B

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat uElt uMat glMat_uElt
  mem_antiSp antiUnipotentCenter transpose_mul_minorJ_mul_apply minorJ_apply)
open CFSG.Quasithin.SteinbergBS (mul_uMat_apply_two mul_uMat_apply_three uMat_mul_apply_zero
  uMat_mul_apply_one uMat_mul_apply_two)
open CFSG.QuasithinUnique.Setup.X7b (uElt_inj uElt_zero_eq_one)
open CFSG.Blueprint (suzukiGroup)
open CFSG.LieType.Ree (suzukiU suzukiSElt mem_suzukiZ0_iff)

variable {k : Type} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem uMat_mul_apply_three (N : Matrix (Fin 4) (Fin 4) k) (a b c d : k) (j : Fin 4) :
    (uMat a b c d * N) 3 j = N 3 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]

theorem isUpper_of_conj_center {d : antiSp k} {b c b' c' : k} (hb : b ≠ 0) (hc : c ≠ 0)
    (hb' : b' ≠ 0) (h : d * uElt 0 b' c' 0 * d⁻¹ = uElt 0 b c 0) : IsUpper d := by
  have h1 : d * uElt 0 b' c' 0 = uElt 0 b c 0 * d := by rw [← h]; group
  have h2 := congrArg (fun g : antiSp k => glMat (g : GL (Fin 4) k)) h1
  have hE : glMat (d : GL (Fin 4) k) * uMat 0 b' c' 0 =
      uMat 0 b c 0 * glMat (d : GL (Fin 4) k) := by
    simpa [glMat_uElt] using h2
  have hJ := mem_antiSp.mp d.2
  have htwo : (2 : k) = 0 := CharTwo.two_eq_zero
  set M := glMat (d : GL (Fin 4) k) with hM
  have entry : ∀ (P Q : Matrix (Fin 4) (Fin 4) k), P = Q → ∀ i j, P i j = Q i j :=
    fun P Q h i j => by rw [h]
  have e22 := entry _ _ hE 2 2
  have e32 := entry _ _ hE 3 2
  have e23 := entry _ _ hE 2 3
  have e33 := entry _ _ hE 3 3
  have e12 := entry _ _ hE 1 2
  have e02 := entry _ _ hE 0 2
  have j02 := entry _ _ hJ 0 2
  rw [mul_uMat_apply_two, uMat_mul_apply_two] at e22
  rw [mul_uMat_apply_two, uMat_mul_apply_three] at e32
  rw [mul_uMat_apply_three, uMat_mul_apply_two] at e23
  rw [mul_uMat_apply_three, uMat_mul_apply_three] at e33
  rw [mul_uMat_apply_two, uMat_mul_apply_one] at e12
  rw [mul_uMat_apply_two, uMat_mul_apply_zero] at e02
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at j02
  norm_num at j02
  have h20 : M 2 0 = 0 :=
    (mul_eq_zero.mp (show M 2 0 * b' = 0 by linear_combination e22)).resolve_right hb'
  have h30 : M 3 0 = 0 :=
    (mul_eq_zero.mp (show M 3 0 * b' = 0 by linear_combination e32)).resolve_right hb'
  have h21 : M 2 1 = 0 :=
    (mul_eq_zero.mp (show M 2 1 * b' = 0 by linear_combination e23 - c' * h20)).resolve_right hb'
  have h31 : M 3 1 = 0 :=
    (mul_eq_zero.mp (show M 3 1 * b' = 0 by linear_combination e33 - c' * h30)).resolve_right hb'
  have E1 : M 1 0 * b' = b * M 3 2 := by linear_combination e12
  have E2 : M 0 0 * b' = b * M 2 2 + c * M 3 2 := by linear_combination e02
  have hS : M 0 0 * M 3 2 + M 1 0 * M 2 2 = 0 := by
    rw [h20, h30] at j02
    linear_combination j02
  have key : c * (M 1 0 * M 3 2) = 0 := by
    linear_combination M 0 0 * E1 - M 1 0 * E2 + b * hS - b * M 1 0 * M 2 2 * htwo
  have hprod : M 1 0 * M 3 2 = 0 := (mul_eq_zero.mp key).resolve_left hc
  have h10 : M 1 0 = 0 := by
    have h3 : M 1 0 * M 1 0 * b' = 0 := by linear_combination M 1 0 * E1 + b * hprod
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hb')
  have h32 : M 3 2 = 0 := by
    have h3 : b * M 3 2 = 0 := by rw [← E1, h10, zero_mul]
    exact (mul_eq_zero.mp h3).resolve_left hb
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij
  exacts [h10, h20, h21, h30, h31, h32]


end CFSG.Quasithin.Ch3E213M.P6B
