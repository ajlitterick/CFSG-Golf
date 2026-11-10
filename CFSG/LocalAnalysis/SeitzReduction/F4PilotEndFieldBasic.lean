module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTransferCyclic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

variable {G X : Type*} [Group G] [Group X] {G₀ : Subgroup G}

@[expose] def normalizerMulAut (e : G₀ ≃* X) : normalizer (G₀ : Set G) →* MulAut X :=
  (MulAut.congr e).toMonoidHom.comp G₀.normalizerMonoidHom

theorem coe_symm_normalizerMulAut_apply (e : G₀ ≃* X) (n : normalizer (G₀ : Set G)) (x : X) :
    ((e.symm (normalizerMulAut e n x) : G₀) : G) = n * (e.symm x : G) * (n : G)⁻¹ := by
  change ((e.symm (e (G₀.normalizerMonoidHom n (e.symm x))) : G₀) : G) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem normalizerMulAut_of_mem (e : G₀ ≃* X) {z : G} (hz : z ∈ G₀) :
    normalizerMulAut e ⟨z, le_normalizer hz⟩ = MulAut.conj (e ⟨z, hz⟩) := by
  apply MulEquiv.ext
  intro w
  apply e.symm.injective
  apply Subtype.ext
  rw [coe_symm_normalizerMulAut_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.symm_apply_apply]
  rfl


section Complement


end Complement


section Endgame


end Endgame

end CFSG.SeitzReduction.F4Pilot
