module

public import CFSG.Quasithin.SteinbergBSConjugateOrbits

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]


theorem le_normalizer_of_forall_conj_mem {S P : Subgroup G}
    (h : ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P) : S ≤ normalizer (P : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro p
  refine ⟨h s hs p, fun hp => ?_⟩
  have h1 := h s⁻¹ (inv_mem hs) _ hp
  simpa [mul_assoc] using h1


end CFSG.Quasithin.SteinbergBS
