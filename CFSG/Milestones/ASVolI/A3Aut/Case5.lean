module

public import CFSG.Milestones.ASVolI.A3Aut.Model

public section

namespace CFSG.ASVolI

open CFSG.Open

section Case5

variable {G : Type} [Group G]


theorem burnsideAut_map_le_normalizer_map {H₁ H₂ : Type*} [Group H₁] [Group H₂] (f : H₁ →* H₂)
    {X Y : Subgroup H₁} (hY : Y ≤ Subgroup.normalizer (X : Set H₁)) :
    Y.map f ≤ Subgroup.normalizer ((X.map f : Subgroup H₂) : Set H₂) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' := hY hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hy'
  conv_rhs => rw [← hy']
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]


end Case5

end CFSG.ASVolI
