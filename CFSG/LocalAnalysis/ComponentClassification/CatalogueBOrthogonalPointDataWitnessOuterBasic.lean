module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CatalogueBStabilizerFamily

universe u v w

variable {G : Type u} [Group G] {D : Type v} [Group D] {X : Type w}

@[expose] def imageNormalizerRangeEquiv (rho : G →* Equiv.Perm X)
    (tau : D →* Equiv.Perm X) (h : rho.range = tau.range) :
    imageNormalizer rho ≃* imageNormalizer tau :=
  MulEquiv.subgroupCongr (congrArg (fun S : Subgroup (Equiv.Perm X) =>
    Subgroup.normalizer (S : Set (Equiv.Perm X))) h)


theorem imageNormalizerRangeEquiv_image (rho : G →* Equiv.Perm X)
    (tau : D →* Equiv.Perm X) (h : rho.range = tau.range) :
    (normalizerImage rho).map (imageNormalizerRangeEquiv rho tau h).toMonoidHom =
      normalizerImage tau := by
  ext phi
  constructor
  · rintro ⟨psi, hpsi, rfl⟩
    change psi.val ∈ tau.range
    rw [← h]
    exact hpsi
  · intro hphi
    refine ⟨(imageNormalizerRangeEquiv rho tau h).symm phi, ?_,
      (imageNormalizerRangeEquiv rho tau h).apply_symm_apply phi⟩
    change phi.val ∈ rho.range
    rw [h]
    exact hphi

@[expose] def normalizerOuterRangeEquiv (rho : G →* Equiv.Perm X)
    (tau : D →* Equiv.Perm X) (h : rho.range = tau.range) :
    normalizerOuter rho ≃* normalizerOuter tau :=
  QuotientGroup.congr (normalizerImage rho) (normalizerImage tau)
    (imageNormalizerRangeEquiv rho tau h) (imageNormalizerRangeEquiv_image rho tau h)


@[expose] def familyOuterRangeEquiv (rho : G →* Equiv.Perm X)
    (tau : D →* Equiv.Perm X) (h : rho.range = tau.range)
    (hrho : Function.Injective rho) (hsrho : Function.Injective (pointStabilizer rho))
    (htau : Function.Injective tau) (hstau : Function.Injective (pointStabilizer tau)) :
    familyOuter rho ≃* familyOuter tau :=
  ((quotientEquiv rho hrho hsrho).trans (normalizerOuterRangeEquiv rho tau h)).trans
    (quotientEquiv tau htau hstau).symm


end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
