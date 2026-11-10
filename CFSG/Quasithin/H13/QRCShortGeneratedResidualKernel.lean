module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBlockCentrality
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Base

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_of_forall_conj_mem {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) : A ≤ normalizer (B : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro b
  refine ⟨h a ha b, fun hb => ?_⟩
  have := h a⁻¹ (inv_mem ha) _ hb
  simpa [mul_assoc] using this


end CFSG.Quasithin.H13.QRC
