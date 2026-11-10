module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalHull
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup CFSG.Assembly

theorem map_subgroupOf_normal {H B : Type*} [Group H] [Group B] (f : H →* B) {D C : Subgroup H}
    (hDC : (D.subgroupOf C).Normal) (hle : D ≤ C) : ((D.map f).subgroupOf (C.map f)).Normal := by
  rw [normal_subgroupOf_iff (map_mono hle)]
  rintro _ _ ⟨d, hd, rfl⟩ ⟨c, hc, rfl⟩
  exact ⟨c * d * c⁻¹, (normal_subgroupOf_iff hle).mp hDC d c hd hc, by
    rw [map_mul, map_mul, map_inv]⟩

theorem map_rangeRestrict_eq_bot_iff {H B : Type*} [Group H] [Group B] (f : H →* B)
    (K : Subgroup H) : K.map f.rangeRestrict = ⊥ ↔ K.map f = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, Subgroup.map_eq_bot_iff, MonoidHom.ker_rangeRestrict]


end CFSG.ComponentClassification.UnbalancingLocal
