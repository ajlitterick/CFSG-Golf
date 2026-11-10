module

public import CFSG.ClassicalInvolution.AschTight.S1916Omega3
public import CFSG.ClassicalInvolution.AschTight.S1916Eta
public import CFSG.ClassicalInvolution.AschTight.S1916Quat

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}
  {Y' Q : Subgroup G}

omit [Finite G] in
theorem USet_mono {Ω Ω₁ : Set (Subgroup G)} (h : Ω ⊆ Ω₁) : USet Ω ⊆ USet Ω₁ := by
  rintro U ⟨R, ⟨J, hJ, P, rfl⟩, hUR, hcyc, hidx⟩
  exact ⟨_, ⟨J, h hJ, P, rfl⟩, hUR, hcyc, hidx⟩


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
