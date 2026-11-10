module

public import CFSG.RankThree.PartTwo.Sec12.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type*} [Group G]

theorem isSylowOf_exists_conj [Finite G] {p : ℕ} [Fact p.Prime] {P P' D : Subgroup G}
    (hP : IsSylowOf p P D) (hP' : IsSylowOf p P' D) :
    ∃ x ∈ D, P' = P.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hP'
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D Q Q'
  refine ⟨d, d.2, ?_⟩
  rw [← hd, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩


theorem map_conj_inf_centralizer {A L : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hL : x ∈ Subgroup.normalizer (L : Set G)) :
    (A ⊓ Subgroup.centralizer (L : Set G)).map (MulAut.conj x).toMonoidHom =
      A ⊓ Subgroup.centralizer (L : Set G) := by
  have key : ∀ y : G, ∀ z ∈ Subgroup.normalizer (A : Set G),
      z ∈ Subgroup.normalizer (L : Set G) → y ∈ A ⊓ Subgroup.centralizer (L : Set G) →
        z * y * z⁻¹ ∈ A ⊓ Subgroup.centralizer (L : Set G) := by
    intro y z hzA hzL hy
    obtain ⟨hyA, hyL⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hzA y).mp hyA, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hyL ⊢
    intro l hl
    have hl' : z⁻¹ * l * z ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hzL) l).mp hl
      simpa using this
    have e := hyL _ hl'
    calc l * (z * y * z⁻¹) = z * ((z⁻¹ * l * z) * y) * z⁻¹ := by group
      _ = z * (y * (z⁻¹ * l * z)) * z⁻¹ := by rw [e]
      _ = z * y * z⁻¹ * l := by group
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact key w x hA hL hw
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := key y x⁻¹ (inv_mem hA) (inv_mem hL) hy
    simpa using this


end CFSG.RankThree.PartTwo.Sec12
