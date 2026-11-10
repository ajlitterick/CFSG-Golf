module

public import CFSG.Monster.B.Dyadic.Data
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.Algebra.BigOperators.Field
public import Certificates.Certificate3106
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Dyadic

open Module CFSG.Monster.B.Dyadic.Native CFSG.KC.BM.Lat

@[expose] def Bq : Matrix (Fin 4371) (Fin 4371) ℚ := fun i j => (Bmat i j : ℚ) / 128

theorem Bmat_lower {i j : Fin 4371} (h : j < i) : Bmat i j = 0 := by
  rw [Bmat_apply, Bz, basis_facts.lower i i.2 j h]
  rfl

theorem Bmat_diag
    (i : Fin 4371) : Bmat i i = 2 ^ diagExpK[(i : ℕ)]! := by
  rw [Bmat_apply, Bz, basis_facts.diag i i.2]
  push_cast
  rfl

theorem Bq_isUpperTriangular :
    Bq.IsUpperTriangular := fun i j h => by
  rw [Bq, Bmat_lower (show j < i from h), Int.cast_zero, zero_div]

theorem diagExp_le
    (i : Fin 4371) : diagExpK[(i : ℕ)]! ≤ 7 := basis_facts.pexp_le i i.2

theorem Bq_diag
    (i : Fin 4371) : Bq i i = ((2 : ℚ) ^ (7 - diagExpK[(i : ℕ)]!))⁻¹ := by
  have h := diagExp_le i
  have e : (128 : ℚ) = 2 ^ diagExpK[(i : ℕ)]! * 2 ^ (7 - diagExpK[(i : ℕ)]!) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
    norm_num
  rw [Bq, Bmat_diag]
  push_cast
  rw [e]
  field_simp

theorem list_sum_range (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.sum_range_succ, Finset.sum_range_succ, list_sum_range f n]

theorem diag_stats :
    (List.range 8).map (expCountOf diagExpK) = [0, 12, 284, 993, 1782, 1035, 243, 22] ∧
      expDefectOf diagExpK = 13123 :=
  Certificates.certificate3103.1

theorem expDefect_eq :
    ∑ i : Fin 4371, (7 - diagExpK[(i : ℕ)]!) = 13123 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => 7 - diagExpK[i]!) 4371, ← list_sum_range]
  exact diag_stats.2

theorem det_Bq :
    Bq.det = ((2 : ℚ) ^ 13123)⁻¹ := by
  rw [Matrix.det_of_isUpperTriangular Bq_isUpperTriangular]
  simp_rw [Bq_diag]
  rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, expDefect_eq]


variable {V : Type*} [AddCommGroup V] [Module ℚ V] (R : Basis (Fin 4371) ℚ V)

theorem ell_eq (i : Fin 4371) : ell R i = ∑ j, Bq i j • R j := by
  rw [ell, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, Bq, one_div, inv_mul_eq_div]
  norm_num

theorem repr_ell (i j : Fin 4371) : R.repr (ell R i) j = Bq i j := by
  rw [ell_eq, Basis.repr_sum_self]

theorem toMatrix_ell : R.toMatrix (ell R) = Bq.transpose := by
  ext i j
  rw [Basis.toMatrix_apply, repr_ell, Matrix.transpose_apply]

theorem det_ell :
    R.det (ell R) = ((2 : ℚ) ^ 13123)⁻¹ := by
  rw [Basis.det_apply, toMatrix_ell, Matrix.det_transpose, det_Bq]

@[expose] noncomputable def ellBasis :
    Basis (Fin 4371) ℚ V :=
  have h := (R.is_basis_iff_det (v := ell R)).2 (by
    rw [det_ell]
    exact isUnit_iff_ne_zero.2 (by positivity))
  Basis.mk h.1 h.2.ge

theorem coe_ellBasis :
    ⇑(ellBasis R) = ell R := by
  unfold ellBasis
  rw [Basis.coe_mk]

theorem ell_linIndep_int :
    LinearIndependent ℤ (ell R) := by
  have := (ellBasis R).linearIndependent
  rw [coe_ellBasis] at this
  exact this.restrict_scalars' ℤ

@[expose] noncomputable def ellZBasis :
    Basis (Fin 4371) ℤ (Lam R) :=
  Basis.span (ell_linIndep_int R)

theorem coe_ellZBasis
    (i : Fin 4371) : (ellZBasis R i : V) = ell R i := by
  unfold ellZBasis
  exact congrArg Subtype.val (Basis.span_apply (ell_linIndep_int R) i)


theorem ell_mem_Lam (i : Fin 4371) : ell R i ∈ Lam R := Submodule.subset_span ⟨i, rfl⟩


@[expose] noncomputable def lamEnd (N : V →ₗ[ℚ] V) (h : ∀ x ∈ Lam R, N x ∈ Lam R) :
    Lam R →ₗ[ℤ] Lam R :=
  (N.restrictScalars ℤ).restrict h

theorem coe_lamEnd (N : V →ₗ[ℚ] V) (h : ∀ x ∈ Lam R, N x ∈ Lam R) (x : Lam R) :
    (lamEnd R N h x : V) = N x := rfl

@[expose] noncomputable def modTwoMap {M : Type*} [AddCommGroup M] (φ : M →ₗ[ℤ] M) :
    ModN M 2 →ₗ[ZMod 2] ModN M 2 :=
  ((LinearMap.range (LinearMap.lsmul ℤ M ((2 : ℕ) : ℤ))).mapQ _ φ (by
    rintro _ ⟨y, rfl⟩
    exact ⟨φ y, by simp⟩)).toAddMonoidHom.toZModLinearMap 2

theorem modTwoMap_mkQ {M : Type*} [AddCommGroup M] (φ : M →ₗ[ℤ] M) (x : M) :
    modTwoMap φ (ModN.mkQ 2 x) = ModN.mkQ 2 (φ x) := rfl

theorem mkQ_zsmul {M : Type*} [AddCommGroup M] (c : ℤ) (x : M) :
    ModN.mkQ 2 (c • x) = (c : ZMod 2) • ModN.mkQ 2 x := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]


theorem Bzq_isUpperTriangular :
    Bzq.IsUpperTriangular := fun i j h => by
  change (Bz i j : ℚ) = 0
  rw [← Bmat_apply, Bmat_lower (show j < i from h), Int.cast_zero]

theorem isUnit_det_Bzq : IsUnit Bzq.det := by
  rw [Matrix.det_of_isUpperTriangular Bzq_isUpperTriangular]
  refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
  change (Bz i i : ℚ) ≠ 0
  rw [← Bmat_apply, Bmat_diag]
  positivity

theorem Cnum_mul_Bzq (g : Fin 26) : Cnum g * Bzq = Bzq * Mq g := by
  rw [Cnum, Matrix.mul_assoc (Bzq * Mq g), Matrix.nonsing_inv_mul (A := Bzq) isUnit_det_Bzq,
    Matrix.mul_one]

theorem Cnum_num (g : Fin 26) (i t : Fin 4371) :
    ((Cnum g i t).num : ℚ) = Cnum g i t :=
  Rat.coe_int_num_of_den_eq_one (Certificates.certificate3106 g i t)

theorem ell_image
    (g : Fin 26) (N : V →ₗ[ℚ] V)
    (hN : ∀ t, N (R t) = ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) (i : Fin 4371) :
    ∃ c : Fin 4371 → ℤ, N (ell R i) = ∑ t, (c t : ℚ) • ell R t ∧
      ∀ t, (c t : ZMod 2) = Cmat g i t := by
  refine ⟨fun t => (Cnum g i t).num, ?_, fun t => rfl⟩
  have hX : ∀ u : Fin 4371, ∑ s : Fin 4371, Bq i s * ((numer g s u : ℚ) / 8) =
      ∑ t : Fin 4371, ((Cnum g i t).num : ℚ) * Bq t u := by
    intro u
    have h := congrFun (congrFun (Cnum_mul_Bzq g) i) u
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    simp only [Cnum_num]
    calc ∑ s : Fin 4371, Bq i s * ((numer g s u : ℚ) / 8) =
        (∑ s : Fin 4371, Bzq i s * Mq g s u) / 128 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun s _ => ?_
          change (Bz i s : ℚ) / 128 * ((numer g s u : ℚ) / 8) =
            (Bz i s : ℚ) * ((numer g s u : ℚ) / 8) / 128
          ring
      _ = (∑ t : Fin 4371, Cnum g i t * Bzq t u) / 128 := by rw [h]
      _ = ∑ t : Fin 4371, Cnum g i t * Bq t u := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun t _ => ?_
          change Cnum g i t * (Bz t u : ℚ) / 128 = Cnum g i t * ((Bz t u : ℚ) / 128)
          ring
  have hL : N (ell R i) =
      ∑ u : Fin 4371, (∑ s : Fin 4371, Bq i s * ((numer g s u : ℚ) / 8)) • R u := by
    rw [ell_eq, map_sum]
    simp_rw [map_smul, hN, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_smul]
  have hR : ∑ t, ((Cnum g i t).num : ℚ) • ell R t =
      ∑ u : Fin 4371, (∑ t, ((Cnum g i t).num : ℚ) * Bq t u) • R u := by
    simp_rw [ell_eq, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_smul]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun u _ => by rw [hX u]

theorem lam_mapsTo
    (g : Fin 26) (N : V →ₗ[ℚ] V)
    (hN : ∀ t, N (R t) = ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) :
    ∀ x ∈ Lam R, N x ∈ Lam R := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => N x ∈ Lam R) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc, -⟩ := ell_image R g N hN i
    rw [hc]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (ell_mem_Lam R t)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [map_zsmul]
    exact Submodule.smul_mem _ a hx

theorem modTwo_ell
    (g : Fin 26) (N : V →ₗ[ℚ] V)
    (hN : ∀ t, N (R t) = ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u)
    (hm : ∀ x ∈ Lam R, N x ∈ Lam R) (k : Fin 4371) :
    modTwoMap (lamEnd R N hm) (ModN.basis (ellZBasis R) k) =
      ∑ l, Cmat g k l • ModN.basis (ellZBasis R) l := by
  rw [ModN.basis_apply_eq_mkQ, modTwoMap_mkQ]
  obtain ⟨c, hc, hpar⟩ := ell_image R g N hN k
  have h' : lamEnd R N hm (ellZBasis R k) = ∑ l, c l • ellZBasis R l := by
    apply Subtype.ext
    rw [Submodule.coe_sum, coe_lamEnd, coe_ellZBasis, hc]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Submodule.coe_smul, coe_ellZBasis, Int.cast_smul_eq_zsmul]
  rw [h', map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mkQ_zsmul, hpar, ModN.basis_apply_eq_mkQ]


end CFSG.Monster.B.Dyadic
