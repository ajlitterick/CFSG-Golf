module

public import CFSG.ClassicalInvolution.Asc77.AscT8Four

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.GH74.Uniqueness CFSG.StronglyEmbedded.UniqueCoset

namespace T8

section PD

variable {G : Type} [Group G] [Finite G]


end PD

section Reduce

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}


end Reduce

end T8

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C27_4b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ∀ g : G, g⁻¹ * (z * t) * g ∈ T8.H274 Ω K z →
        Subgroup.centralizer ({g⁻¹ * (z * t) * g} : Set G) ≤ T8.H274 Ω K z

variable {p f}

theorem c27_4b_of_c27_4a (h : C27_4a p f) : C27_4b p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc g hg c hc
  have hfix : (z * t) • ((g : G) : G ⧸ T8.H274 Ω K z) = (g : G ⧸ T8.H274 Ω K z) :=
    (smul_coe_eq_iff _ _ g).2 hg
  have hAH : z * t ∈ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hs.hJ hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hfix1 : (z * t) • (((1 : G)) : G ⧸ T8.H274 Ω K z) = ((1 : G) : G ⧸ T8.H274 Ω K z) :=
    (smul_coe_eq_iff _ _ 1).2 (by simpa using hAH)
  have hgH : g ∈ T8.H274 Ω K z := by
    have := (h G Ω K J S R T W z t hs hdisc).unique hfix hfix1
    have h2 := QuotientGroup.eq.1 this
    simpa using h2
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hcg : g * c * g⁻¹ ∈ Subgroup.centralizer ({z * t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * c * g⁻¹ * (z * t) = g * (c * (g⁻¹ * (z * t) * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * (z * t) * g) * c) * g⁻¹ := by rw [hc]
      _ = (z * t) * (g * c * g⁻¹) := by group
  have h3 := T8.centralizer_mul_le_H274 (z := z) hs.hJ hs.ht hcg
  have h4 := (T8.H274 Ω K z).mul_mem ((T8.H274 Ω K z).mul_mem ((T8.H274 Ω K z).inv_mem hgH) h3) hgH
  simpa [mul_assoc] using h4


end CFSG.ClassicalInvolution.Asc77
