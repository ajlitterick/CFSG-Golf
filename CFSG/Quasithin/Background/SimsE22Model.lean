module

public import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.Quasithin.SimsE22

open CFSG.Open

section PrimeSubfield

variable (F : Type) [Field F]

@[expose] noncomputable def primeEmb : GL (Fin 2) (⊥ : Subfield F) →* GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.map (⊥ : Subfield F).subtype

@[expose] noncomputable def primeProj :
    GL (Fin 2) (⊥ : Subfield F) →* Matrix.ProjGenLinGroup (Fin 2) F :=
  Matrix.ProjGenLinGroup.mk.comp (primeEmb F)

theorem primeEmb_apply (B : GL (Fin 2) (⊥ : Subfield F)) (i j : Fin 2) :
    ((primeEmb F B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      (((B : Matrix (Fin 2) (Fin 2) (⊥ : Subfield F)) i j : (⊥ : Subfield F)) : F) :=
  Matrix.GeneralLinearGroup.map_apply _ i j B

theorem mem_range_primeEmb {A : GL (Fin 2) F} :
    A ∈ (primeEmb F).range ↔
      ∀ i j, (A : Matrix (Fin 2) (Fin 2) F) i j ∈ (⊥ : Subfield F) := by
  constructor
  · rintro ⟨B, rfl⟩ i j
    rw [primeEmb_apply]
    exact (B : Matrix (Fin 2) (Fin 2) (⊥ : Subfield F)) i j |>.2
  · intro hA
    let B : Matrix (Fin 2) (Fin 2) (⊥ : Subfield F) := Matrix.of fun i j => ⟨A i j, hA i j⟩
    have hBA : (⊥ : Subfield F).subtype.mapMatrix B = (A : Matrix (Fin 2) (Fin 2) F) := by
      ext i j; rfl
    have hdet : B.det ≠ 0 := by
      intro h
      have := RingHom.map_det (⊥ : Subfield F).subtype B
      rw [h, map_zero, hBA] at this
      exact Matrix.GeneralLinearGroup.det_ne_zero A this.symm
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B hdet, ?_⟩
    ext i j
    rw [primeEmb_apply]
    rfl

theorem coe_scalar_mul_apply (u : Fˣ) (A : GL (Fin 2) F) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u * A : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) i j = (u : F) * (A : Matrix (Fin 2) (Fin 2) F) i j := by
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul]

theorem coe_mul_scalar_apply (u : Fˣ) (A : GL (Fin 2) F) (i j : Fin 2) :
    ((A * Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) i j = (A : Matrix (Fin 2) (Fin 2) F) i j * (u : F) := by
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_diagonal]

theorem mk_mem_range_primeProj_iff {A : GL (Fin 2) F} :
    Matrix.ProjGenLinGroup.mk A ∈ (primeProj F).range ↔
      ∃ c : Fˣ, ∀ i j, (c : F) * (A : Matrix (Fin 2) (Fin 2) F) i j ∈ (⊥ : Subfield F) := by
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 hB
    refine ⟨u⁻¹, fun i j => ?_⟩
    have h1 : (A : Matrix (Fin 2) (Fin 2) F) i j =
        (primeEmb F B : Matrix (Fin 2) (Fin 2) F) i j * (u : F) := by
      rw [← coe_mul_scalar_apply, hu]
    have h2 : ((u⁻¹ : Fˣ) : F) * (A : Matrix (Fin 2) (Fin 2) F) i j =
        (primeEmb F B : Matrix (Fin 2) (Fin 2) F) i j := by
      rw [h1, Units.val_inv_eq_inv_val]
      field_simp
    rw [h2]
    exact (mem_range_primeEmb F).1 ⟨B, rfl⟩ i j
  · rintro ⟨c, hc⟩
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) c * A ∈ (primeEmb F).range :=
      (mem_range_primeEmb F).2 fun i j => by rw [coe_scalar_mul_apply]; exact hc i j
    obtain ⟨B, hB⟩ := h1
    refine ⟨B, ?_⟩
    simp only [primeProj, MonoidHom.comp_apply, hB]
    rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

@[expose] def primeScaled : Subgroup (GL (Fin 2) F) where
  carrier := {A | ∃ c : Fˣ, ∀ i j,
    (c : F) * (A : Matrix (Fin 2) (Fin 2) F) i j ∈ (⊥ : Subfield F)}
  one_mem' := (mk_mem_range_primeProj_iff F).1 (by rw [map_one]; exact one_mem _)
  mul_mem' := fun {A B} hA hB => (mk_mem_range_primeProj_iff F).1 (by
    rw [map_mul]
    exact mul_mem ((mk_mem_range_primeProj_iff F).2 hA) ((mk_mem_range_primeProj_iff F).2 hB))
  inv_mem' := fun {A} hA => (mk_mem_range_primeProj_iff F).1 (by
    rw [map_inv]
    exact inv_mem ((mk_mem_range_primeProj_iff F).2 hA))


@[expose] def X0 : Subgroup (StatedProj (StatedSL 2 F)) :=
  ((primeScaled F).subgroupOf (StatedSL 2 F)).map (QuotientGroup.mk' _)

section Membership


end Membership


end PrimeSubfield

section MainResults


end MainResults

section Unipotent


end Unipotent

end CFSG.Quasithin.SimsE22
