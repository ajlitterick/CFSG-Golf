module

public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.Quasithin.SimsG4

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]


theorem isImprimitiveOnV_of_family {G₀ : Subgroup (V ≃ₗ[F] V)} {ι : Type*} [Finite ι]
    (hι : 1 < Nat.card ι) (U : ι → Submodule F V) (hU0 : ∀ i, U i ≠ ⊥) (hind : iSupIndep U)
    (hsup : (⨆ i, U i) = ⊤) (hperm : ∀ g ∈ G₀, ∀ i, ∃ j, (U i).map (g : V →ₗ[F] V) = U j) :
    IsImprimitiveOnV G₀ := by
  let e := Finite.equivFin ι
  refine ⟨Nat.card ι, U ∘ e.symm, hι, fun i => hU0 _, hind.comp e.symm.injective, ?_, ?_⟩
  · rw [← hsup]
    exact e.symm.iSup_comp (g := U)
  · intro g hg i
    obtain ⟨j, hj⟩ := hperm g hg (e.symm i)
    exact ⟨e j, by simp only [Function.comp_apply, Equiv.symm_apply_apply, hj]⟩


end CFSG.Quasithin.SimsG4
