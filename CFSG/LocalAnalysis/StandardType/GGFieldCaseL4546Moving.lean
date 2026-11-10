module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type} [Group G]

theorem exists_pow_pow_ne_one {p : ℕ} {w : G} (hw : ∃ n : ℕ, w ^ p ^ n = 1) (hw1 : w ≠ 1) :
    ∃ m : ℕ, w ^ p ^ m ≠ 1 ∧ (w ^ p ^ m) ^ p = 1 := by
  classical
  have hn0 : Nat.find hw ≠ 0 := by
    intro h0
    have := Nat.find_spec hw
    rw [h0, pow_zero, pow_one] at this
    exact hw1 this
  refine ⟨Nat.find hw - 1, Nat.find_min hw (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
  exact Nat.find_spec hw

theorem mem_normalizer_zpowers_of_conj_mem [Finite G] {p : ℕ} [Fact p.Prime] {d e r : G}
    (hdp : d ^ p = 1) (he : e ∈ Subgroup.zpowers d) (he1 : e ≠ 1)
    (hre : r * e * r⁻¹ ∈ Subgroup.zpowers d) :
    r ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  have hre1 : r * e * r⁻¹ ≠ 1 := fun h => he1 (by
    have := congrArg (fun g => r⁻¹ * g * r) h
    simpa [mul_assoc] using this)
  have h1 := zpowers_eq_of_mem_of_ne_one hdp he he1
  have h2 := zpowers_eq_of_mem_of_ne_one hdp hre hre1
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← h1] at hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← h2, ← conj_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  · intro hg
    rw [← h2] at hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [conj_zpow] at hk
    have hg' : g = e ^ k := by
      have := congrArg (fun z => r⁻¹ * z * r) hk
      simpa [mul_assoc] using this.symm
    rw [hg', ← h1]
    exact Subgroup.zpow_mem_zpowers _ k

end General

section Moving


end Moving


end CFSG.StandardType

end
