module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open Module Matrix

@[expose] def d5Index : Fin 5 → Fin 6 := fun i => Fin.succ i

@[expose] def d5Cartan : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j => CartanMatrix.E 6 (d5Index i) (d5Index j)

@[expose] def d5Cartan3 : Matrix (Fin 5) (Fin 5) (ZMod 3) :=
  fun i j => (d5Cartan i j : ZMod 3)

theorem d5Cartan3_det_ne_zero : d5Cartan3.det ≠ 0 := by
  change (Matrix.of fun i j => (CartanMatrix.E 6 (Fin.succ i) (Fin.succ j) : ZMod 3)).det ≠ 0
  decide +kernel

theorem e6Cartan_reindex {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = CoxeterMatrix.E₆.reindex e) :
    ∀ i j : Fin 6, CL (e i) (e j) = CartanMatrix.E 6 i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hCL.1]
    fin_cases i <;> decide
  · have heij : e i ≠ e j := fun h => hij (e.injective h)
    have h₂ : GGIntCartan ML (Matrix.reindex e e (CartanMatrix.E 6)) := by
      rw [hML]
      exact GGIntCartan.reindex e ggIntCartan_E₆
    have hMle : ML.M (e i) (e j) ≤ 3 := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      fin_cases i <;> fin_cases j <;> decide
    have h1 := (hCL.pair h₂ heij).2 hMle
    rw [h1.1]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem d5_roots_linearIndependent
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) :
    LinearIndependent (ZMod 3) (fun i : Fin 5 => h (d5Index i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcM : d5Cartan3 *ᵥ c = 0 := by
    ext j
    have h := congrArg (α (d5Index j)) hc
    simp only [map_sum, map_smul, hpair, smul_eq_mul, map_zero] at h
    simpa only [d5Cartan3, d5Cartan, d5Index, Matrix.mulVec, dotProduct,
      Finset.sum_apply, Pi.zero_apply, mul_comm] using h
  intro i
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero d5Cartan3_det_ne_zero hcM) i

theorem axis_not_mem_d5_span
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V} {y : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hy : y ≠ 0) (hker : ∀ i, α i y = 0) :
    y ∉ Submodule.span (ZMod 3) (Set.range (fun i : Fin 5 => h (d5Index i))) := by
  intro hmem
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hcM : d5Cartan3 *ᵥ c = 0 := by
    ext j
    have h := congrArg (α (d5Index j)) hc
    simp only [map_sum, map_smul, hpair, smul_eq_mul, hker, map_zero] at h
    simpa [d5Cartan3, d5Cartan, d5Index, Matrix.mulVec, dotProduct, mul_comm] using h
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero d5Cartan3_det_ne_zero hcM
  rw [hc0] at hc
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hc
  exact hy hc.symm

theorem d5_axis_linearIndependent
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V} {y : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hy : y ≠ 0) (hker : ∀ i, α i y = 0) :
    LinearIndependent (ZMod 3) (fun o : Option (Fin 5) =>
      o.casesOn' y (fun i => h (d5Index i))) :=
  (d5_roots_linearIndependent hpair).option (axis_not_mem_d5_span hpair hy hker)


end CFSG.StandardType
