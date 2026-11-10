module

public import CFSG.ClassicalInvolution.Asc77.WP1Section7
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
public import CFSG.ClassicalInvolution.AschTight.Sec7L713C

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]


variable {p f : ℕ} [Fact p.Prime]


theorem exists_zpowers_eq {A : Subgroup G} (hA : IsCyclic ↥A) :
    ∃ u : G, Subgroup.zpowers u = A := by
  obtain ⟨g, hg⟩ := hA.exists_generator
  refine ⟨g, le_antisymm (Subgroup.zpowers_le.mpr g.2) fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [← Subgroup.coe_zpow, hn]⟩

theorem eq_closure_of_index_two {A R : Subgroup G} (h2 : A.relIndex R = 2) (hAR : A ≤ R)
    {u r : G} (hu : Subgroup.zpowers u = A) (hrR : r ∈ R) (hrA : r ∉ A) :
    R = Subgroup.closure {u, r} := by
  have huc : u ∈ Subgroup.closure ({u, r} : Set G) := Subgroup.subset_closure (by simp)
  have hrc : r ∈ Subgroup.closure ({u, r} : Set G) := Subgroup.subset_closure (by simp)
  have hAc : A ≤ Subgroup.closure {u, r} := hu ▸ Subgroup.zpowers_le.mpr huc
  refine le_antisymm (fun ρ hρ => ?_) ((Subgroup.closure_le _).mpr ?_)
  · rcases mem_or_mul_inv_mem_of_relIndex_two h2 hrR hrA hρ with h | h
    · exact hAc h
    · have e : ρ = ρ * r⁻¹ * r := by group
      rw [e]
      exact Subgroup.mul_mem _ (hAc h) hrc
  · intro x hx
    rcases hx with rfl | rfl
    · exact hAR (hu ▸ Subgroup.mem_zpowers x)
    · exact hrR


theorem braid_of_order_three {Q : Type*} [Group Q] {x y : Q} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) ^ 3 = 1) : y * x * y = x * y * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : x * y * x * (y * x * y) = 1 := by
    rw [pow_three] at hxy
    calc x * y * x * (y * x * y) = x * y * (x * y * (x * y)) := by group
      _ = 1 := hxy
  calc y * x * y = (x * y * x)⁻¹ * (x * y * x * (y * x * y)) := by group
    _ = (x * y * x)⁻¹ := by rw [h1, mul_one]
    _ = x⁻¹ * y⁻¹ * x⁻¹ := by group
    _ = x * y * x := by rw [hxi, hyi]

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
