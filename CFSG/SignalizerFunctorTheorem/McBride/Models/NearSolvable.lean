module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Sections
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

open NearSolvable


theorem isSolvable_of_lt_top_sz {n : ℕ} (hp : (2 * n + 1).Prime)
    (hY : signalizerNearPSolvable (2 * n + 1) (Sz n)) (H : Subgroup (Sz n)) (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  by_contra hns
  have hcard := card_sz n
  have hp2 : 2 * n + 1 ≠ 2 := by omega
  have hodd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hp1 : 1 ≤ 2 * n + 1 := by omega
  have h3 := two_pow_mod_three hodd
  obtain ⟨S, _, hSmodel, hSdvd⟩ := exists_model_card_dvd_of_not_isSolvable hY H hns
  have hdvd := hSdvd.trans (Subgroup.card_subgroup_dvd_card H)
  rw [hcard] at hdvd
  rcases nearSimpleModel_card hp hp2 hSmodel with h | h | h | h
  · rw [h] at hdvd
    exact not_three_dvd_suzuki h3
      ((((three_dvd_sq_sub_one h3).mul_left _).trans hdvd))
  · rw [h] at hdvd
    exact not_three_dvd_suzuki h3
      (((dvd_pow_self 3 hp.ne_zero).trans ((three_pow_dvd_psl2_three _).trans hdvd)))
  · exact hH (eq_top_of_card_dvd (by rw [hcard, ← h]; exact hSdvd))
  · rw [h] at hdvd
    exact not_two_pow_two_mul_succ_dvd_suzuki hp1
      ((two_pow_two_mul_succ_dvd_cube hp1).trans ((two_pow_cube_dvd_psu3 hodd).trans hdvd))


end CFSG.SignalizerFunctorTheorem.McBride
