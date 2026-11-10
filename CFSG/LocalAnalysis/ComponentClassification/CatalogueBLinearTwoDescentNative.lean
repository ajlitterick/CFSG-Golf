module

import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGammaL2ProjectiveHilbert90
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoDescent

noncomputable section

open CFSG.GorensteinWalter

universe u


theorem native_semilinear_involution_conjugacy
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (a : PGammaL2 K) (ha : orderOf a = 2) (hfield : a.right ≠ 1) :
    ∃ h : PGL2 K,
      a = SemidirectProduct.inl h * SemidirectProduct.inr a.right *
        (SemidirectProduct.inl h)⁻¹ := by
  obtain ⟨h, hh⟩ :=
    CFSG.GorensteinWalter.projective_semilinear_involution_conj_inr
      hK a ha hfield
  refine ⟨h, ?_⟩
  calc
    a = SemidirectProduct.inl h *
        ((SemidirectProduct.inl h)⁻¹ * a * SemidirectProduct.inl h) *
        (SemidirectProduct.inl h)⁻¹ := by group
    _ = _ := by rw [hh]


end

end CFSG.ComponentClassification.CatalogueBLinearTwoDescent
