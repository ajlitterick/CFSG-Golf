module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneTorus
public import CFSG.LinearAlgebra.ProjectivePrimePlane

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup

variable {K : Type*} [Field K] {p : ℕ} [NeZero p]

omit [NeZero p] in
theorem scalar_mem_center' (u : Kˣ) :
    GeneralLinearGroup.scalar (Fin p) u ∈ Subgroup.center (GL (Fin p) K) := by
  rw [GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨u, rfl⟩

omit [NeZero p] in
theorem mul_scalar_comm (u : Kˣ) (g : GL (Fin p) K) :
    g * GeneralLinearGroup.scalar (Fin p) u = GeneralLinearGroup.scalar (Fin p) u * g :=
  Subgroup.mem_center_iff.1 (scalar_mem_center' u) g

theorem scalar_injective' :
    Function.Injective (GeneralLinearGroup.scalar (Fin p) : Kˣ →* GL (Fin p) K) := by
  intro u v h
  have h1 := congrArg (fun g : GL (Fin p) K => (g : Matrix (Fin p) (Fin p) K) 0 0) h
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h1
  exact Units.ext h1

variable (P : GL (Fin p) K)

omit [NeZero p] in
theorem exists_scalar_of_commute_torus {M : GL (Fin p) K} {x : Fin p → Kˣ}
    (h : torusHom P x * mk M = mk M * torusHom P x) :
    ∃ c : Kˣ, (P⁻¹ * (M : GL (Fin p) K) * P) * TauCeti.diagGL x =
      GeneralLinearGroup.scalar (Fin p) c *
        (TauCeti.diagGL x * (P⁻¹ * (M : GL (Fin p) K) * P)) := by
  rw [torusHom_apply] at h
  obtain ⟨u, hu⟩ := CFSG.LinearAlgebra.ProjectivePrimePlane.exists_mul_eq_smul_of_commute h
  have hMA := CFSG.LinearAlgebra.ProjectivePrimePlane.mul_eq_scalar_mul_of_val hu
  refine ⟨u, ?_⟩
  calc (P⁻¹ * (M : GL (Fin p) K) * P) * TauCeti.diagGL x =
      P⁻¹ * (M * (P * TauCeti.diagGL x * P⁻¹)) * P := by group
    _ = P⁻¹ * GeneralLinearGroup.scalar (Fin p) u *
        ((P * TauCeti.diagGL x * P⁻¹) * M) * P := by rw [hMA]; group
    _ = GeneralLinearGroup.scalar (Fin p) u * P⁻¹ *
        ((P * TauCeti.diagGL x * P⁻¹) * M) * P := by rw [mul_scalar_comm]
    _ = _ := by group


@[expose] def rootVec (ζ : Kˣ) : Fin p → Kˣ := fun i => ζ ^ (i : ℕ)

abbrev frameElt (ζ : Kˣ) : ProjGenLinGroup (Fin p) K :=
  torusHom P (rootVec ζ)

abbrev framePre (ζ : Kˣ) : Subgroup (GL (Fin p) K) :=
  (Subgroup.centralizer {frameElt P ζ}).comap mk

variable (ζ : Kˣ)

omit [NeZero p] in
theorem framePre_rel [NeZero p] (M : framePre P ζ) :
    ∃ c : Kˣ, (P⁻¹ * (M : GL (Fin p) K) * P) * TauCeti.diagGL (rootVec ζ) =
      GeneralLinearGroup.scalar (Fin p) c *
        (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * (M : GL (Fin p) K) * P)) :=
  exists_scalar_of_commute_torus P (Subgroup.mem_centralizer_iff.1 M.2 _ rfl)

@[expose] noncomputable def frameScalarFun (M : framePre P ζ) : Kˣ :=
  (framePre_rel P ζ M).choose

theorem frameScalarFun_spec (M : framePre P ζ) :
    (P⁻¹ * (M : GL (Fin p) K) * P) * TauCeti.diagGL (rootVec ζ) = GeneralLinearGroup.scalar (Fin p)
      (frameScalarFun P ζ M) * (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * (M : GL (Fin p) K) * P)) :=
  (framePre_rel P ζ M).choose_spec

omit [NeZero p] in
theorem frame_scalar_unique [NeZero p] {N : GL (Fin p) K} {c c' : Kˣ}
    (h : N * TauCeti.diagGL (rootVec ζ) =
      GeneralLinearGroup.scalar (Fin p) c * (TauCeti.diagGL (rootVec ζ) * N))
    (h' : N * TauCeti.diagGL (rootVec ζ) =
      GeneralLinearGroup.scalar (Fin p) c' * (TauCeti.diagGL (rootVec ζ) * N)) : c = c' :=
  scalar_injective' (mul_right_cancel (h.symm.trans h'))

theorem frameScalarFun_eq (M : framePre P ζ) {c : Kˣ}
    (h : (P⁻¹ * (M : GL (Fin p) K) * P) * TauCeti.diagGL (rootVec ζ) =
      GeneralLinearGroup.scalar (Fin p) c *
        (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * (M : GL (Fin p) K) * P))) :
    frameScalarFun P ζ M = c :=
  frame_scalar_unique ζ (frameScalarFun_spec P ζ M) h

@[expose] noncomputable def frameScalarHat : framePre P ζ →* Kˣ where
  toFun := frameScalarFun P ζ
  map_one' := frameScalarFun_eq P ζ 1 (by
    rw [OneMemClass.coe_one, mul_one, inv_mul_cancel, map_one, one_mul, one_mul, mul_one])
  map_mul' M₁ M₂ := by
    refine frameScalarFun_eq P ζ (M₁ * M₂) ?_
    have h1 := frameScalarFun_spec P ζ M₁
    have h2 := frameScalarFun_spec P ζ M₂
    have hN : P⁻¹ * ((M₁ * M₂ : framePre P ζ) : GL (Fin p) K) * P =
        (P⁻¹ * (M₁ : GL (Fin p) K) * P) * (P⁻¹ * (M₂ : GL (Fin p) K) * P) := by
      rw [Subgroup.coe_mul]
      group
    set D := TauCeti.diagGL (rootVec ζ)
    set N₁ := P⁻¹ * (M₁ : GL (Fin p) K) * P
    set N₂ := P⁻¹ * (M₂ : GL (Fin p) K) * P
    set S₁ := GeneralLinearGroup.scalar (Fin p) (frameScalarFun P ζ M₁)
    set S₂ := GeneralLinearGroup.scalar (Fin p) (frameScalarFun P ζ M₂)
    have hc : ∀ g : GL (Fin p) K, g * S₂ = S₂ * g := fun g => mul_scalar_comm _ g
    rw [hN, map_mul]
    calc N₁ * N₂ * D = N₁ * (N₂ * D) := by group
      _ = N₁ * (S₂ * (D * N₂)) := by rw [h2]
      _ = N₁ * S₂ * (D * N₂) := by group
      _ = S₂ * N₁ * (D * N₂) := by rw [hc N₁]
      _ = S₂ * (N₁ * D) * N₂ := by group
      _ = S₂ * (S₁ * (D * N₁)) * N₂ := by rw [h1]
      _ = S₂ * S₁ * (D * (N₁ * N₂)) := by group
      _ = S₁ * S₂ * (D * (N₁ * N₂)) := by rw [hc S₁]


theorem ker_mk_le_ker_frameScalarHat :
    (mk.subgroupComap (Subgroup.centralizer {frameElt P ζ})).ker ≤
      (frameScalarHat P ζ).ker := by
  intro M hM
  rw [MonoidHom.mem_ker] at hM ⊢
  have hM' : mk (M : GL (Fin p) K) = 1 := congrArg Subtype.val hM
  rw [mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hM'
  obtain ⟨u, hu⟩ := hM'
  refine frameScalarFun_eq P ζ M ?_
  have hPs : P⁻¹ * GeneralLinearGroup.scalar (Fin p) u * P =
      GeneralLinearGroup.scalar (Fin p) u := by
    rw [mul_assoc, ← mul_scalar_comm u P, inv_mul_cancel_left]
  rw [← hu, hPs, map_one, one_mul]
  exact (mul_scalar_comm u _).symm

@[expose] noncomputable def frameScalar :
    Subgroup.centralizer {frameElt P ζ} →* Kˣ :=
  (mk.subgroupComap (Subgroup.centralizer {frameElt P ζ})).liftOfSurjective
    (mk.subgroupComap_surjective _ mk_surjective)
    ⟨frameScalarHat P ζ, ker_mk_le_ker_frameScalarHat P ζ⟩


end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
