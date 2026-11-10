module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Fus
public import CFSG.ClassicalInvolution.Asc77.AscT7ERFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]


theorem c25_17_norm_of_11_16 (h11 : C25_11 p f) (h16 : C25_16 p f) : C25_17_norm p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  obtain ⟨t', ht'S, ⟨g, hg⟩, hconj⟩ := c25_2_t_proved p f G Ω K K' W S R R' z t u₁ u₂ hyp
  have hzz : z * z = 1 := hyp.std.setting.hz.sq
  have ht'2 : t' * t' = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' := ⟨hyp, ht'S, ht'2, hconj⟩
  by_contra hlt
  push Not at hlt
  exact h.false_of_d8 h11 h16 hlt

theorem c25_17_idx_of_11_16 (h11 : C25_11 p f) (h16 : C25_16 p f) : C25_17_idx p f :=
  c25_17_idx_of_norm p f (c25_17_norm_of_11_16 p f h11 h16)


end CFSG.ClassicalInvolution.Asc77
