module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement


theorem exists_sylow_map_eq {E Q : Type*} [Group E] [Group Q] [Finite E] {ℓ : ℕ}
    [Fact ℓ.Prime] {η : E →* Q} (hη : Function.Surjective η) (S : Sylow ℓ Q) :
    ∃ T : Sylow ℓ E, (T : Subgroup E).map η = S := by
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hη ℓ S
  exact ⟨T, by rw [← hT, Sylow.coe_mapSurjective]⟩


end CFSG.LocalAnalysis.ComponentInitial
