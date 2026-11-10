module

public import Mathlib.Basic.Finite.Prod
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Coset.Defs

public section

namespace CFSG.Quasithin.SimsD1.Embed


theorem exists_of_le_map {G : Type} [Group G] {G₁ T : Subgroup G} {F : Type} [Group F]
    {ι₁ : ↥G₁ →* F} (hι : Function.Injective ι₁) (hT₁ : T ≤ G₁) {N : Subgroup F}
    (hN : N ≤ (T.subgroupOf G₁).map ι₁) :
    ∃ K : Subgroup G, K ≤ T ∧ N = (K.subgroupOf G₁).map ι₁ := by
  have hle : N.comap ι₁ ≤ T.subgroupOf G₁ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hN hx
    obtain rfl : y = x := hι hxy
    exact hy
  refine ⟨(N.comap ι₁).map G₁.subtype, ?_, ?_⟩
  · calc (N.comap ι₁).map G₁.subtype ≤ (T.subgroupOf G₁).map G₁.subtype := Subgroup.map_mono hle
      _ = T ⊓ G₁ := Subgroup.subgroupOf_map_subtype T G₁
      _ = T := inf_of_le_left hT₁
  · have h : ((N.comap ι₁).map G₁.subtype).subgroupOf G₁ = N.comap ι₁ :=
      Subgroup.comap_map_eq_self_of_injective G₁.subtype_injective _
    rw [h]
    exact (Subgroup.map_comap_eq_self (hN.trans (Subgroup.map_le_range _ _))).symm

end CFSG.Quasithin.SimsD1.Embed
