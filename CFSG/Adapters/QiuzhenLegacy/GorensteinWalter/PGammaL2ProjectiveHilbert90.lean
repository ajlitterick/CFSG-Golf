module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

public section

namespace CFSG

noncomputable section

namespace GorensteinWalter

open scoped MatrixGroups

universe u


private def twistedProd {K : Type u} [Field K] (σ : K ≃+* K) (A : GL (Fin 2) K) :
    ℕ → GL (Fin 2) K
  | 0 => 1
  | n + 1 => A * Matrix.GeneralLinearGroup.map σ.toRingHom (twistedProd σ A n)

private theorem twistedProd_coe {K : Type u} [Field K] (σ : K ≃+* K) (A : GL (Fin 2) K)
    (n : ℕ) : ((twistedProd σ A n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      HardMathSupport.Foote.ModuleExclusions.Ai σ (A : Matrix (Fin 2) (Fin 2) K) n := by
  induction n with
  | zero => simp [twistedProd, HardMathSupport.Foote.ModuleExclusions.Ai]
  | succ n ih =>
    have h1 : ((twistedProd σ A (n + 1) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K) *
          ((twistedProd σ A n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map σ := by
      ext i j
      simp [twistedProd, Matrix.mul_apply]
    rw [h1, ih]
    rfl

private theorem pow_left_eq_twistedProd {K : Type u} [Field K] (x : PGammaL2 K)
    (A : GL (Fin 2) K) (hA : Matrix.ProjGenLinGroup.mk A = x.left) (n : ℕ) :
    (x ^ n).left = Matrix.ProjGenLinGroup.mk (twistedProd x.right A n) := by
  induction n with
  | zero => simp [twistedProd]
  | succ n ih =>
    rw [pow_succ', SemidirectProduct.mul_left, ih, pgl2FieldAut_apply, ← hA]
    have : pgl2RingEquiv x.right (Matrix.ProjGenLinGroup.mk (twistedProd x.right A n)) =
        Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map x.right.toRingHom
          (twistedProd x.right A n)) := pgl2RingEquiv_mk x.right (twistedProd x.right A n)
    rw [this, ← map_mul]
    rfl

theorem pGammaL2_conj_inr_of_pow_eq_one {K : Type u} [Field K] [Finite K] (x : PGammaL2 K)
    (hx : x ^ orderOf x.right = 1) :
    ∃ C : PGL2 K, (SemidirectProduct.inl C)⁻¹ * x * SemidirectProduct.inl C =
      SemidirectProduct.inr x.right := by
  set σ := x.right with hσ
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective x.left
  have hAd : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    simpa using A.det.ne_zero
  have hone : (x ^ orderOf σ).left = 1 := by rw [hx]; rfl
  rw [pow_left_eq_twistedProd x A hA] at hone
  have hcenter : twistedProd σ A (orderOf σ) ∈ Subgroup.center (GL (Fin 2) K) :=
    Matrix.ProjGenLinGroup.mk_eq_one.mp hone
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨u, hu⟩ := hcenter
  have hcoe : HardMathSupport.Foote.ModuleExclusions.Ai σ (A : Matrix (Fin 2) (Fin 2) K)
      (orderOf σ) = (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← twistedProd_coe, ← hu]
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    rw [Matrix.smul_one_eq_diagonal]
  obtain ⟨l, B, hl0, hB, hAB⟩ :=
    HardMathSupport.Foote.ModuleExclusions.hilbert90_matrix σ (A : Matrix (Fin 2) (Fin 2) K)
      hAd (u : K) hcoe
  let B' : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB
  refine ⟨Matrix.ProjGenLinGroup.mk B', ?_⟩
  have hxeq : x = SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk A) *
      SemidirectProduct.inr σ := by
    rw [hA]; exact (SemidirectProduct.inl_left_mul_inr_right x).symm
  have hAB' : A * Matrix.GeneralLinearGroup.map σ.toRingHom B' =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)) * B' := by
    apply Units.ext
    have h1 : (l • (A : Matrix (Fin 2) (Fin 2) K)) * B.map σ = B := hAB
    have h2 : (A : Matrix (Fin 2) (Fin 2) K) * B.map σ = l⁻¹ • B := by
      rw [← one_smul K ((A : Matrix (Fin 2) (Fin 2) K) * B.map σ), ← inv_mul_cancel₀ hl0,
        mul_smul, ← Matrix.smul_mul, h1]
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h3
    simp [B', Matrix.mul_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply, h3]
  have heq : B'⁻¹ * A * Matrix.GeneralLinearGroup.map σ.toRingHom B' =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)) := by
    have hz : Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)) ∈
        Subgroup.center (GL (Fin 2) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    have hc := Subgroup.mem_center_iff.mp hz B'⁻¹
    rw [mul_assoc, hAB', ← mul_assoc, hc, mul_assoc, inv_mul_cancel, mul_one]
  have key : (Matrix.ProjGenLinGroup.mk B')⁻¹ * Matrix.ProjGenLinGroup.mk A *
      (pgl2FieldAut K σ) (Matrix.ProjGenLinGroup.mk B') = 1 := by
    have hmapB : pgl2RingEquiv σ (Matrix.ProjGenLinGroup.mk B') =
        Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map σ.toRingHom B') :=
      pgl2RingEquiv_mk σ B'
    rw [pgl2FieldAut_apply, hmapB, ← map_inv, ← map_mul, ← map_mul, heq]
    exact Matrix.ProjGenLinGroup.mk_scalar _
  have hinr : (SemidirectProduct.inr σ : PGammaL2 K) *
      SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk B') =
      SemidirectProduct.inl ((pgl2FieldAut K σ) (Matrix.ProjGenLinGroup.mk B')) *
        SemidirectProduct.inr σ := by
    rw [SemidirectProduct.inl_aut, map_inv]
    group
  conv_lhs => rw [hxeq]
  calc (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk B') : PGammaL2 K)⁻¹ *
        (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk A) * SemidirectProduct.inr σ) *
          SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk B') =
      (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk B') : PGammaL2 K)⁻¹ *
        SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk A) *
          (SemidirectProduct.inr σ * SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk B')) := by
        group
    _ = (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk B') : PGammaL2 K)⁻¹ *
        SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk A) *
          (SemidirectProduct.inl ((pgl2FieldAut K σ) (Matrix.ProjGenLinGroup.mk B')) *
            SemidirectProduct.inr σ) := by rw [hinr]
    _ = SemidirectProduct.inl ((Matrix.ProjGenLinGroup.mk B')⁻¹ *
          Matrix.ProjGenLinGroup.mk A * (pgl2FieldAut K σ) (Matrix.ProjGenLinGroup.mk B')) *
            SemidirectProduct.inr σ := by
        simp only [map_mul, map_inv, mul_assoc]
    _ = SemidirectProduct.inr σ := by rw [key]; simp

theorem pGammaL2_involution_conj_inr_of_finite {K : Type u} [Field K] [Finite K]
    (x : PGammaL2 K) (hx : orderOf x = 2) (hfield : x.right ≠ 1) :
    ∃ C : PGL2 K, (SemidirectProduct.inl C)⁻¹ * x * SemidirectProduct.inl C =
      SemidirectProduct.inr x.right := by
  apply pGammaL2_conj_inr_of_pow_eq_one
  have hord : orderOf x.right ∣ orderOf x := orderOf_map_dvd SemidirectProduct.rightHom x
  rw [hx] at hord
  have h2 : orderOf x.right = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hfield
    · exact h
  rw [h2]
  have := pow_orderOf_eq_one x
  rwa [hx] at this

theorem pGammaL2_involution_conj_inr
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (x : PGammaL2 K) (hx : orderOf x = 2) (hfield : x.right ≠ 1) :
    ∃ C : PGL2 K,
      (SemidirectProduct.inl C)⁻¹ * x * SemidirectProduct.inl C =
        SemidirectProduct.inr x.right :=
  pGammaL2_involution_conj_inr_of_finite x hx hfield

end GorensteinWalter

end

end CFSG
