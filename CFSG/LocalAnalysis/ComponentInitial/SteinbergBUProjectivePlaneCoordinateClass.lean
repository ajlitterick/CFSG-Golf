module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneTorus
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralLift
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXClassicalTorus

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup CFSG.LocalAnalysis.GorensteinLyons

variable {K : Type*} [Field K] {p : ℕ}


variable {S : Type*} [Group S]

theorem conj_apply_eq_mul_conj_mul_inv (σ : MulAut S) (a : S) :
    MulAut.conj (σ a) = σ * MulAut.conj a * σ⁻¹ := by
  apply MulEquiv.ext
  intro y
  change σ a * y * (σ a)⁻¹ = σ (a * σ.symm y * a⁻¹)
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem apply_eq_of_commute_conj
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S)) {σ : MulAut S} {a : S}
    (h : σ * MulAut.conj a = MulAut.conj a * σ) : σ a = a := by
  apply hinj
  rw [conj_apply_eq_mul_conj_mul_inv, h, mul_inv_cancel_right]


end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
