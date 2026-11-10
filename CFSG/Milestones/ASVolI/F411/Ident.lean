module

public import CFSG.Milestones.ASVolI.F411.Red

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

section Generic

variable {E : Type} [Group E]


theorem burnsideF411_le_normalizer {K S : Subgroup E}
    (h : ∀ y ∈ K, ∀ s ∈ S, y * s * y⁻¹ ∈ S) : K ≤ Subgroup.normalizer (S : Set E) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨h y hy s, fun hs => ?_⟩
  have := h y⁻¹ (K.inv_mem hy) _ hs
  simpa [mul_assoc] using this


end Generic

section Main


end Main

end CFSG.ASVolI
