module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit Matrix

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_eq_zero_of_le {ρ : Representation (ZMod 2) Γ W} (h : Z1 ρ ≤ B1 ρ) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  have htop : (B1 ρ).comap (Z1 ρ).subtype = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact h x.2
  have : Subsingleton (H1 ρ) := Submodule.Quotient.subsingleton_iff.2 htop
  exact Module.finrank_zero_of_subsingleton

theorem Z1_le_B1_of_central (ρ : Representation (ZMod 2) Γ W) (z : Γ)
    (hc : ∀ g, z * g = g * z) (hbij : Function.Bijective fun w => ρ z w - w) :
    Z1 ρ ≤ B1 ρ := by
  intro f hf
  obtain ⟨m, hm⟩ := hbij.2 (f z)
  refine ⟨m, funext fun g => ?_⟩
  change ρ g m - m = f g
  apply hbij.1
  change ρ z (ρ g m - m) - (ρ g m - m) = ρ z (f g) - f g
  have h1 : f (z * g) = f z + ρ z (f g) := hf z g
  have h2 : f (g * z) = f g + ρ g (f z) := hf g z
  rw [hc g] at h1
  have h3 : ρ z (f g) - f g = ρ g (f z) - f z := by
    have := h1.symm.trans h2
    linear_combination (norm := abel_nf) this
  rw [h3, ← hm]
  have hzg : ρ z (ρ g m) = ρ g (ρ z m) := by
    rw [← Module.End.mul_apply, ← map_mul, hc g, map_mul, Module.End.mul_apply]
  simp only [map_sub, hzg]
  abel


end CFSG.Quasithin.SteinbergCB.I16
