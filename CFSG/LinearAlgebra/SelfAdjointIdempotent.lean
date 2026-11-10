module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

public section

namespace CFSG.LinearAlgebra

open Matrix

variable {K : Type*} [Field K] {n r : ℕ}


theorem eq_zero_of_forall_dotProduct_mulVec_eq_zero {F : Matrix (Fin n) (Fin n) K}
    (hF : IsUnit F) {y : Fin n → K} (hy : ∀ z, z ⬝ᵥ F *ᵥ y = 0) : y = 0 := by
  have h1 : F *ᵥ y = 0 := dotProduct_eq_zero_iff.mp fun z => by rw [dotProduct_comm]; exact hy z
  exact mulVec_injective_iff_isUnit.mpr hF (h1.trans (mulVec_zero F).symm)

theorem eq_zero_of_forall_dotProduct_mulVec_eq_zero' {F : Matrix (Fin n) (Fin n) K}
    (hF : IsUnit F) {x : Fin n → K} (hx : ∀ z, x ⬝ᵥ F *ᵥ z = 0) : x = 0 := by
  have h1 : x ᵥ* F = 0 := dotProduct_eq_zero_iff.mp fun z => by
    rw [← dotProduct_mulVec]
    exact hx z
  exact vecMul_injective_iff_isUnit.mpr hF (h1.trans (zero_vecMul F).symm)

theorem exists_mul_eq_of_range_le {m p : ℕ} {A : Matrix (Fin n) (Fin m) K}
    {B : Matrix (Fin n) (Fin p) K}
    (h : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    ∃ M : Matrix (Fin p) (Fin m) K, B * M = A := by
  have hv : ∀ j, ∃ v, B *ᵥ v = A *ᵥ Pi.single j 1 := fun j => h ⟨Pi.single j 1, rfl⟩
  choose v hv using hv
  refine ⟨Matrix.of fun i j => v j i, Matrix.ext fun i j => ?_⟩
  have h1 := congrFun (hv j) i
  rw [mulVec_single_one, col_apply] at h1
  rw [← h1, Matrix.mul_apply, mulVec, dotProduct]
  rfl


section Conj

variable {F E gm gi : Matrix (Fin n) (Fin n) K} (h1 : gm * gi = 1) (h2 : gi * gm = 1)
include h2

theorem conj_mul_self (hE2 : E * E = E) : gm * E * gi * (gm * E * gi) = gm * E * gi := by
  calc gm * E * gi * (gm * E * gi) = gm * E * (gi * gm) * E * gi := by
        simp only [Matrix.mul_assoc]
    _ = gm * E * gi := by rw [h2, Matrix.mul_one, Matrix.mul_assoc gm, hE2]


theorem range_conj :
    LinearMap.range (gm * E * gi).mulVecLin = (LinearMap.range E.mulVecLin).map gm.mulVecLin := by
  have htop : LinearMap.range gi.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr fun v => ⟨gm *ᵥ v, by rw [mulVecLin_apply, mulVec_mulVec, h2,
      one_mulVec]⟩
  rw [Matrix.mul_assoc, mulVecLin_mul, LinearMap.range_comp, mulVecLin_mul,
    LinearMap.range_comp_of_range_eq_top _ htop]

omit h2 in
include h1 in
theorem rank_conj : (gm * E * gi).rank = E.rank := by
  rw [rank_mul_eq_left_of_isUnit_det gi _ (isUnit_det_of_left_inverse h1),
    rank_mul_eq_right_of_isUnit_det gm _ (isUnit_det_of_right_inverse h1)]

omit h2 in
theorem range_mul_eq_map (U : Matrix (Fin n) (Fin r) K) :
    LinearMap.range (gm * U).mulVecLin = (LinearMap.range U.mulVecLin).map gm.mulVecLin := by
  rw [mulVecLin_mul, LinearMap.range_comp]


end Conj


end CFSG.LinearAlgebra
