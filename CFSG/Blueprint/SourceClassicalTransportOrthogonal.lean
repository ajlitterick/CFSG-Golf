module

public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.Blueprint.SourceQuadraticClassification
public import CFSG.LieType.Universal.IrreducibleQuadratic

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Assembly.LowTwoRank Module Matrix QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadOdd quadMinus coe_quadPlus coe_quadOdd
  coe_quadMinus)

section OrthGroups

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι]
  [DecidableEq ι]

@[expose] def matrixOrthogonal (Q₀ : (ι → K) → K) : Subgroup (GL ι K) where
  carrier := {A | ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v}
  mul_mem' {A B} hA hB v := by
    change Q₀ (((A * B : GL ι K) : Matrix ι ι K) *ᵥ v) = Q₀ v
    rw [Units.val_mul, ← mulVec_mulVec, hA, hB]
  one_mem' v := by
    change Q₀ (((1 : GL ι K) : Matrix ι ι K) *ᵥ v) = Q₀ v
    rw [Units.val_one, one_mulVec]
  inv_mem' {A} hA v := by
    change Q₀ (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = Q₀ v
    have h := hA (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h
    exact h.symm

theorem statedOmega_eq_commutator (Q₀ : (ι → K) → K) :
    StatedOmega Q₀ = ⁅matrixOrthogonal Q₀, matrixOrthogonal Q₀⁆ := by
  have h : Subgroup.closure {A : GL ι K | ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v} =
      matrixOrthogonal Q₀ :=
    Subgroup.closure_eq (matrixOrthogonal Q₀)
  rw [StatedOmega, h]

theorem equivFun_sourceGLEquiv_symm (b : Basis ι K V) (A : GL ι K) (x : V) :
    b.equivFun ((((sourceGLEquiv b).symm A : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) x) = (A : Matrix ι ι K) *ᵥ b.equivFun x := by
  have hg : LinearMap.toMatrix b b (((sourceGLEquiv b).symm A :
      LinearMap.GeneralLinearGroup K V) : Module.End K V) = A := by
    rw [← coe_sourceGLEquiv, MulEquiv.apply_symm_apply]
  rw [← hg]
  exact (LinearMap.toMatrix_mulVec_repr b b _ x).symm

theorem map_sourceOrthogonal (b : Basis ι K V) {Q : V → K} {Q₀ : (ι → K) → K}
    (hQ : ∀ x, Q x = Q₀ (b.equivFun x)) :
    (sourceOrthogonal Q).map (sourceGLEquiv b).toMonoidHom = matrixOrthogonal Q₀ := by
  ext A
  rw [Subgroup.mem_map_equiv]
  change (∀ x, Q ((((sourceGLEquiv b).symm A : LinearMap.GeneralLinearGroup K V) :
    Module.End K V) x) = Q x) ↔ ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v
  simp only [hQ, equivFun_sourceGLEquiv_symm]
  refine ⟨fun H v => ?_, fun H x => H _⟩
  have := H (b.equivFun.symm v)
  rwa [LinearEquiv.apply_symm_apply] at this

theorem map_sourceOmega (b : Basis ι K V) {Q : V → K} {Q₀ : (ι → K) → K}
    (hQ : ∀ x, Q x = Q₀ (b.equivFun x)) :
    ⁅sourceOrthogonal Q, sourceOrthogonal Q⁆.map (sourceGLEquiv b).toMonoidHom =
      StatedOmega Q₀ := by
  rw [Subgroup.map_commutator, map_sourceOrthogonal b hQ, statedOmega_eq_commutator]


end OrthGroups


theorem nonempty_statedProj_statedOmega_equiv {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (Q₀ : (ι → K) → K) :
    Nonempty (StatedProj (StatedOmega Q₀) ≃*
      (⁅sourceOrthogonal Q₀, sourceOrthogonal Q₀⁆ : Subgroup _) ⧸
        (sourceScalars K (ι → K)).subgroupOf ⁅sourceOrthogonal Q₀, sourceOrthogonal Q₀⁆) := by
  refine ⟨quotientInfCongr (sourceGLEquiv (Pi.basisFun K ι)).symm ?_ ?_⟩
  · rw [← map_sourceOmega (Pi.basisFun K ι) (Q₀ := Q₀) fun x => rfl, Subgroup.map_map]
    simp
  · rw [← map_sourceScalars_sourceGLEquiv (Pi.basisFun K ι), Subgroup.map_map]
    simp


theorem nonempty_sourceOmega_equiv_minus {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (hn : 1 ≤ n)
    (hV : finrank K V = 2 * n) {Q : V → K} (hQ : IsSourceQuadratic Q)
    (hw : sourceWittIndex Q = n - 1) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nonempty ((⁅sourceOrthogonal Q, sourceOrthogonal Q⁆ : Subgroup _) ⧸
        (sourceScalars K V).subgroupOf ⁅sourceOrthogonal Q, sourceOrthogonal Q⁆ ≃*
      StatedProj (StatedOmega (StatedQuadMinus n K b c))) := by
  have hnd := hQ.nondegenerate (Or.inr ⟨n, by omega⟩)
  obtain ⟨iso⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType hnd hn hV
    (hQ.not_isPlusType hn hV hw) hirr
  let bs : Basis (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K V := Basis.ofEquivFun iso.toLinearEquiv
  have hQb : ∀ x, Q x = StatedQuadMinus n K b c (bs.equivFun x) := fun x => by
    rw [Basis.equivFun_ofEquivFun, ← coe_quadMinus]
    exact (iso.map_app x).symm
  exact ⟨quotientInfCongr (sourceGLEquiv bs) (map_sourceOmega bs hQb)
    (map_sourceScalars_sourceGLEquiv bs)⟩


theorem nonempty_statedOmegaMinus_equiv {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    {b c b' c' : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hirr' : ∀ s : K, s ^ 2 + b' * s + c' ≠ 0) :
    Nonempty (StatedProj (StatedOmega (StatedQuadMinus n K b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus n K b' c'))) := by
  obtain ⟨e₁⟩ := nonempty_statedProj_statedOmega_equiv (StatedQuadMinus n K b c)
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have hQ : IsSourceQuadratic (StatedQuadMinus n K b c) := by
    rw [← coe_quadMinus]
    exact isSourceQuadratic_of_nondegenerate _ hnd
  obtain ⟨e₂⟩ := nonempty_sourceOmega_equiv_minus hn (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]
      omega) hQ (sourceWittIndex_statedQuadMinus n K hn hirr) hirr'
  exact ⟨e₁.trans e₂⟩

end CFSG.Blueprint.EvenSource
