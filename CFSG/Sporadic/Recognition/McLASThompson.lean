module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2
public import CFSG.Sporadic.Recognition.McLASThreeLocalPinned

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup

theorem ThreeLocal.thompsonAbelianSubgroups_eq {G : Type*} [Group G] {x : G}
    {R T A : Subgroup G} (h : ThreeLocal G x R T A) :
    CFSG.thompsonAbelianSubgroups T = {A} := by
  have hAab : IsMulCommutative ↥A := h.A_elementaryAbelian.toIsMulCommutative
  ext B
  constructor
  · rintro ⟨hBT, hBab, hmax⟩
    have h1 := (h.abelian_subgroups B hBT hBab).1
    have h2 := hmax A h.A_le_T hAab
    rw [h.card_A] at h2
    exact (h.abelian_subgroups B hBT hBab).2 (le_antisymm h1 h2)
  · intro hB
    rw [Set.mem_singleton_iff] at hB
    subst hB
    refine ⟨h.A_le_T, hAab, fun B' hB'T hB'ab => ?_⟩
    rw [h.card_A]
    exact (h.abelian_subgroups B' hB'T hB'ab).1

theorem ThreeLocal.thompsonSubgroup_eq {G : Type*} [Group G] {x : G}
    {R T A : Subgroup G} (h : ThreeLocal G x R T A) : CFSG.thompsonSubgroup T = A := by
  change sSup (CFSG.thompsonAbelianSubgroups T) = A
  rw [h.thompsonAbelianSubgroups_eq, sSup_singleton]


end CFSG.Sporadic.Recognition.McLAS
