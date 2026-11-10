module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL43Hard
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseQuot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type*} [Group G]

theorem exists_maxPSubgroup_of_le [Finite G] {p : ℕ} {H Q : Subgroup G} (hQ : IsPGroup p Q)
    (hQH : Q ≤ H) :
    ∃ R : Subgroup G, IsPGroup p R ∧ Q ≤ R ∧ R ≤ H ∧
      ∀ S : Subgroup G, S ≤ H → IsPGroup p S → R ≤ S → S = R := by
  obtain ⟨R, hR⟩ := (Set.toFinite {R : Subgroup G | IsPGroup p R ∧ Q ≤ R ∧ R ≤ H}).exists_maximal
    ⟨Q, hQ, le_rfl, hQH⟩
  exact ⟨R, hR.1.1, hR.1.2.1, hR.1.2.2, fun S hSH hS hRS =>
    le_antisymm (hR.2 ⟨hS, hR.1.2.1.trans hRS, hSH⟩ hRS) hRS⟩

theorem le_normalizer_of_maxPSubgroup {p : ℕ} {C R U : Subgroup G}
    (hRC : R ≤ Subgroup.normalizer (C : Set G)) (hR : IsPGroup p R) (hUR : U ≤ R) (hUC : U ≤ C)
    (hmax : ∀ Q : Subgroup G, Q ≤ C → IsPGroup p Q → U ≤ Q → Q = U) :
    R ≤ Subgroup.normalizer (U : Set G) := by
  have hU : R ⊓ C = U := hmax _ inf_le_right (hR.to_le inf_le_left) (le_inf hUR hUC)
  intro r hr
  rw [← hU, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨R.mul_mem (R.mul_mem hr h1) (R.inv_mem hr),
      (Subgroup.mem_normalizer_iff.mp (hRC hr) h).mp h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hRC hr) h).mpr h2⟩
    have := R.mul_mem (R.mul_mem (R.inv_mem hr) h1) hr
    simpa [mul_assoc] using this

theorem ggNormalizer_le_normalizer_centralizer (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hh s hs
    have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
    have h1 := hh _ hs'
    calc s * (g * h * g⁻¹) = g * ((g⁻¹ * s * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * h * g⁻¹ * s := by group
  · intro hh s hs
    have hs' : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hg s).mp hs
    have h1 := hh _ hs'
    calc s * h = g⁻¹ * ((g * s * g⁻¹) * (g * h * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * h * g⁻¹) * (g * s * g⁻¹)) * g := by rw [h1]
      _ = h * s := by group

theorem le_normalizer_zpowers_of_le {S U : Subgroup G} {d : G} (hd : d ∈ S)
    (hU : U ≤ Subgroup.centralizer (S : Set G)) :
    U ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  intro u hu
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hdu : d * u = u * d := Subgroup.mem_centralizer_iff.mp (hU hu) d hd
  exact (Commute.zpow_left hdu k).eq

end General


end CFSG.StandardType

end
