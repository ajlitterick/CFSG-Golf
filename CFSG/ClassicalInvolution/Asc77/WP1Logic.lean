module

public import CFSG.ClassicalInvolution.Asc77.AscSteps181

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]


theorem e18_8z_of_e18_7 (h : E18_7 p f) : E18_8z p f := by
  intro G _ _ Ω K S R W H c a hz
  have ha1 : a ≠ 1 := hz.ne_one
  have ha2 : a * a = 1 := hz.sq
  have hcent : Subgroup.centralizer ({a} : Set G) ≤ H := c.centralizer_le p f hz
  have haH : a ∈ H := hcent (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have h7 := h G Ω K S R W H c a ha1 ha2 hcent
  refine ⟨(1 : G) , ?_, ?_⟩
  · show a • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact QuotientGroup.eq.mpr (by simpa using H.inv_mem haH)
  · intro c' hc'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c'
    have hg : g⁻¹ * a * g ∈ H := by
      have h1 : a • ((g : G) : G ⧸ H) = (g : G ⧸ H) := hc'
      rw [MulAction.Quotient.smul_mk, smul_eq_mul] at h1
      have h2 := QuotientGroup.eq.mp h1
      have : (a * g)⁻¹ * g = g⁻¹ * a⁻¹ * g := by group
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
      rw [this, ha'] at h2
      exact h2
    obtain ⟨k, hk, hka⟩ := h7 g⁻¹ (by simpa using hg)
    have hgk : g * k ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 : k * a * k⁻¹ = g⁻¹ * a * g := by simpa using hka
      calc (g * k) * a = (g * (k * a * k⁻¹)) * k := by group
        _ = a * (g * k) := by rw [h3]; group
    have : g ∈ H := by
      have h4 : g * k * k⁻¹ ∈ H := H.mul_mem (hcent hgk) (H.inv_mem hk)
      simpa using h4
    exact (QuotientGroup.eq.mpr (by simpa using H.inv_mem this)).symm

end CFSG.ClassicalInvolution.Asc77
