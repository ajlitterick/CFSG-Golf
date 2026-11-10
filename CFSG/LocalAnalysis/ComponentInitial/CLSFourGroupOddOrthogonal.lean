module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal

open Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CatalogueBOrthogonalSemilinear
  CatalogueBOrthogonalInvolutionRepresentation CatalogueBOrthogonalPointData
  CatalogueBOrthogonalDescent CatalogueBLinearTwoDescent CatalogueBHigherLinearField
open CLSFourGroupScalarSquare FixedFourGroup FourGroupOddBilinear
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Commutant

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def commutant (τ : V ≃+ V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x, g (τ x) = τ (g x)}
  one_mem' _ := rfl
  mul_mem' {g h} hg hh x := by
    change g (h (τ x)) = τ (g (h x))
    rw [hh, hg]
  inv_mem' {g} hg x := by
    apply g.injective
    change g (g.symm (τ x)) = g (τ (g.symm x))
    rw [hg, g.apply_symm_apply, g.apply_symm_apply]

theorem mem_commutant {τ : V ≃+ V} {g : V ≃ₗ[K] V} :
    g ∈ commutant τ ↔ ∀ x, g (τ x) = τ (g x) :=
  Iff.rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem signEquiv_apply_basis (c : Basis ι K V) (S : Finset ι) (i : ι) :
    signEquiv c S (c i) = (if i ∈ S then -1 else 1 : K) • c i := by
  rw [← LinearEquiv.coe_coe, coe_signEquiv, Matrix.toLin_self, Finset.sum_eq_single i]
  · simp [signDiag_apply]
  · intro j _ hji
    simp [signDiag_apply, hji]
  · intro h
    exact absurd (Finset.mem_univ i) h


end Commutant

section Diagonal

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]


end Diagonal

section Bridge

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

omit Q in
theorem matrixLinearEquiv_scalar (c : Kˣ) (v : Fin d → K) :
    matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) c) v = (c : K) • v := by
  rw [matrixLinearEquiv_apply]
  funext i
  simp [GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]

theorem map_matrixDerived :
    (matrixDerived Q).map matrixLinearIso.toMonoidHom = orthogonalOmega Q := by
  rw [matrixDerived, Subgroup.map_commutator, matrixIsometries,
    Subgroup.map_comap_eq_self_of_surjective (f := matrixLinearIso.toMonoidHom)
      matrixLinearIso.surjective]

@[expose] def derivedEquiv : matrixDerived Q ≃* orthogonalOmega Q :=
  (matrixLinearIso.subgroupMap (matrixDerived Q)).trans
    (MulEquiv.subgroupCongr (map_matrixDerived Q))

theorem derivedEquiv_val (X : matrixDerived Q) :
    ((derivedEquiv Q X : orthogonalOmega Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      matrixLinearEquiv X.val :=
  rfl

theorem matrixLinearEquiv_derivedEquiv_symm (u : orthogonalOmega Q) :
    matrixLinearEquiv ((derivedEquiv Q).symm u).val = u := by
  rw [← derivedEquiv_val, MulEquiv.apply_symm_apply]

theorem map_matrixDerivedScalars (hd : 0 < d) :
    (matrixDerivedScalars Q).map (derivedEquiv Q).toMonoidHom = omegaScalars Q := by
  ext h
  rw [Subgroup.mem_map_equiv, mem_matrixDerivedScalars_iff, mem_omegaScalars]
  have h1 := matrixLinearEquiv_derivedEquiv_symm Q h
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, LinearMap.ext fun v => ?_⟩
    rw [← h1, ← hc]
    exact matrixLinearEquiv_scalar c v
  · rintro ⟨c, hc⟩
    have hv : ∀ v, (h : (Fin d → K) ≃ₗ[K] (Fin d → K)) v = c • v := fun v =>
      LinearMap.congr_fun hc v
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h0 := hv (Pi.single ⟨0, hd⟩ 1)
      rw [zero_smul, LinearEquiv.map_eq_zero_iff] at h0
      simpa using congrFun h0 ⟨0, hd⟩
    refine ⟨Units.mk0 c hc0, matrixLinearIso.injective (LinearEquiv.ext fun v => ?_)⟩
    change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0)) v =
      matrixLinearEquiv ((derivedEquiv Q).symm h).val v
    rw [h1, hv]
    exact matrixLinearEquiv_scalar _ v

@[expose] def projEquiv (hd : 0 < d) : matrixProjectiveDerived Q ≃* OrthogonalProj Q :=
  QuotientGroup.congr (matrixDerivedScalars Q) (omegaScalars Q) (derivedEquiv Q)
    (map_matrixDerivedScalars Q hd)

theorem projEquiv_proj (hd : 0 < d) (X : matrixDerived Q) :
    projEquiv Q hd (matrixProjectiveProjection Q X) = orthogonalProj Q (derivedEquiv Q X) :=
  QuotientGroup.congr_mk' _ _ _ _ X

theorem projEquiv_symm_proj (hd : 0 < d) (u : orthogonalOmega Q) :
    (projEquiv Q hd).symm (orthogonalProj Q u) =
      matrixProjectiveProjection Q ((derivedEquiv Q).symm u) := by
  rw [MulEquiv.symm_apply_eq, projEquiv_proj, MulEquiv.apply_symm_apply]

theorem map_le_fixed (hd : 0 < d) (g : similarityPairs Q)
    {C : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))}
    (hC : ∀ u ∈ C, ∀ v, u (coordinateSemilinearMap g.val v) = coordinateSemilinearMap g.val (u v))
    {W : Subgroup (OrthogonalProj Q)}
    (hW : W ≤ (C.subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q)) :
    W.map (projEquiv Q hd).symm.toMonoidHom ≤
      fixedSubgroup (matrixProjectiveConjugationHom Q g) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨u, hu, rfl⟩ := hW hw
  change matrixProjectiveConjugation Q g ((projEquiv Q hd).symm (orthogonalProj Q u)) =
    (projEquiv Q hd).symm (orthogonalProj Q u)
  rw [projEquiv_symm_proj, matrixProjectiveConjugation_mk]
  refine congrArg _ (Subtype.ext (matrixLinearIso.injective (LinearEquiv.ext fun v => ?_)))
  change matrixLinearEquiv (matrixConjugation g.val ((derivedEquiv Q).symm u).val) v =
    matrixLinearEquiv ((derivedEquiv Q).symm u).val v
  rw [matrixConjugation_vector, matrixLinearEquiv_derivedEquiv_symm,
    ← hC _ (Subgroup.mem_subgroupOf.1 hu), AddEquiv.apply_symm_apply]

end Bridge

theorem isSymm_polarBilin {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : LinearMap.BilinForm.IsSymm Q.polarBilin :=
  ⟨fun x y => QuadraticMap.polar_comm Q x y⟩

section Cases


end Cases


end CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal
