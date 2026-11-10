module

import CFSG.Quasithin.Background.A3Structure36AList
public import CFSG.Quasithin.Background.A3Structure315Defs
public import CFSG.Quasithin.Background.A3StructureFacts

public section

namespace CFSG.Quasithin

namespace A315

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem pResidualOf_eq_bot_of_isPGroup {G : Type*} [Group G] {p : ℕ} {B : Subgroup G}
    (hB : IsPGroup p ↥B) : pResidualOf p B = ⊥ := by
  have h : pResidual p ↥B = ⊥ := by
    refine le_bot_iff.1 (pResidual_le (N := ⊥) fun x => ?_)
    obtain ⟨k, hk⟩ := hB x
    exact ⟨k, by rw [hk]; exact Subgroup.one_mem _⟩
  unfold pResidualOf
  rw [h, Subgroup.map_bot]


end A315

end CFSG.Quasithin
