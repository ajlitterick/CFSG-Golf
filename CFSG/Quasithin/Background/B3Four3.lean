module

public import CFSG.Quasithin.Background.B3Four2
public import CFSG.Quasithin.Background.B3Named6
public import CFSG.Quasithin.Background.B3Two

public section

namespace CFSG.Quasithin.B3

open scoped commutatorElement

variable {k : Mod}


theorem normal_subgroupOf_of_conj {G : Type*} [Group G] {J Y : Subgroup G}
    (h : ∀ x ∈ Y, ∀ j ∈ J, x * j * x⁻¹ ∈ J) : (J.subgroupOf Y).Normal := by
  refine ⟨fun j hj x => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hj ⊢
  simpa using h x x.2 j hj


end CFSG.Quasithin.B3
