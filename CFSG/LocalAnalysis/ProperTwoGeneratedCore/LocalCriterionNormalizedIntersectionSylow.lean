module

public import Mathlib.GroupTheory.Sylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersection

universe u

variable {G : Type u} [Group G] {p : ℕ}


theorem sylow_intersection_extension (X E : Subgroup G)
    (Q : Sylow p (X ⊓ E : Subgroup G)) :
    ∃ P : Sylow p E,
      ((P : Subgroup E).map E.subtype) ⊓ X =
        (Q : Subgroup (X ⊓ E : Subgroup G)).map (X ⊓ E).subtype := by
  let f : (X ⊓ E : Subgroup G) →* E := Subgroup.inclusion inf_le_right
  obtain ⟨P, hP⟩ := Q.exists_comap_eq_of_injective
    (Subgroup.inclusion_injective (inf_le_right : X ⊓ E ≤ E))
  refine ⟨P, ?_⟩
  ext x
  constructor
  · rintro ⟨hxP, hxX⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxP
    have hxE : x ∈ E := hyx ▸ y.property
    let d : (X ⊓ E : Subgroup G) := ⟨x, hxX, hxE⟩
    have hfd : f d = y := Subtype.ext hyx.symm
    have hd : d ∈ (Q : Subgroup (X ⊓ E : Subgroup G)) := by
      rw [← hP]
      change f d ∈ (P : Subgroup E)
      rw [hfd]
      exact hy
    exact Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
  · intro hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨Subgroup.mem_map.mpr ⟨f d, ?_, rfl⟩, d.property.1⟩
    change d ∈ (P : Subgroup E).comap f
    rw [hP]
    exact hd

end CFSG.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersection
