module

public import CFSG.Quasithin.Background.ONanE68LieBar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxSL2

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6.E68Proof
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem subgroupOf_normalizer_eq {L S : Subgroup G} (hSL : S ≤ L) :
    (L ⊓ Subgroup.normalizer (S : Set G)).subgroupOf L =
      Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff,
    Subgroup.mem_normalizer_iff]
  constructor
  · rintro ⟨-, h⟩ y
    have := h (y : G)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact this
  · intro h
    refine ⟨g.2, fun y => ?_⟩
    constructor
    · intro hy
      have := (h ⟨y, hSL hy⟩).1 (by rw [Subgroup.mem_subgroupOf]; exact hy)
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    · intro hy
      have hyL : y ∈ L := by
        have h1 : (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem g.2) (hSL hy)) g.2
        simpa [mul_assoc] using h1
      have := (h ⟨y, hyL⟩).2 (by rw [Subgroup.mem_subgroupOf]; exact hy)
      rw [Subgroup.mem_subgroupOf] at this
      exact this


end CFSG.Quasithin.RonanE611
