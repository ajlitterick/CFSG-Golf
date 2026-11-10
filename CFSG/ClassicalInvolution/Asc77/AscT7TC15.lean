module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7T

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}

theorem exists_hyp25T (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) :
    ∃ t' : G, T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' := by
  obtain ⟨t', ht'S, ⟨g, hg⟩, hconj⟩ := c25_2_t_proved p f G Ω K K' W S R R' z t u₁ u₂ hyp
  have hzz : z * z = 1 := hyp.std.setting.hz.sq
  have ht'2 : t' * t' = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  exact ⟨t', hyp, ht'S, ht'2, hconj⟩


end T7T

end CFSG.ClassicalInvolution.Asc77
