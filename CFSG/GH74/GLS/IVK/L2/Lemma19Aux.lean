module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.ABGDGroups.LinearStructure

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup Matrix CFSG CFSG.GorensteinWalter CFSG.ABGDGroups

section Residual

variable {X : Type*} [Group X]

theorem oPrimeResidual_normal_gen (p : ℕ) : (oPrimeResidual p X).Normal := by
  constructor
  intro n hn g
  unfold oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨k, ?_⟩
    rw [conj_pow, hk]
    group
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem mem_oPrimeResidual_of_pow {p k : ℕ} {x : X} (h : x ^ (p ^ k) = 1) :
    x ∈ oPrimeResidual p X :=
  Subgroup.subset_closure ⟨k, h⟩

end Residual

section PGLResidual

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem exists_involution_psl2 :
    ∃ y : PSL2 F, y ≠ 1 ∧ (Matrix.ProjectiveSpecialLinearGroup.toPGL y) ^ 2 = 1 := by
  let w₀ : SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  let u : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨QuotientGroup.mk' _ w₀, ?_, ?_⟩
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) (h u)
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
    simp [w₀, u, Matrix.mul_apply, Fin.sum_univ_two] at h1
  · rw [← map_pow, ← map_pow]
    have : (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)) (w₀ ^ 2)) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hw : ((w₀ ^ 2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
        rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [w₀, Matrix.mul_apply, Fin.sum_univ_two]
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hw]
      simp
    rw [this, map_one]


end PGLResidual

end CFSG.GH74.GLS.IVK
