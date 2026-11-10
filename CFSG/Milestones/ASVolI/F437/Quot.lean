module

public import CFSG.Milestones.ASVolI.F437.Gen
public import CFSG.Milestones.ASVolI.F48.Core

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

section Quot

variable {E : Type} [Group E]

@[expose] def burnsideF437_c (fb : E) : ↥(f437Ebar fb) :=
  ⟨fb, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem burnsideF437_c_central (fb : E) :
    Subgroup.zpowers (burnsideF437_c fb) ≤ Subgroup.center ↥(f437Ebar fb) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_singleton_iff.mp x.2)

theorem burnsideF437_c_normal (fb : E) : (Subgroup.zpowers (burnsideF437_c fb)).Normal :=
  ⟨fun n hn g => by
    have := burnsideF437_c_central fb hn
    rw [Subgroup.mem_center_iff] at this
    rw [this g, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩


end Quot

section QuotMaps

variable {E : Type} [Group E] {fb : E}

attribute [local instance] burnsideF437_c_normal


end QuotMaps

section Assembly

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {fb : E}

attribute [local instance] burnsideF437_c_normal


end Assembly

end CFSG.ASVolI
