module

public import CFSG.ClassicalInvolution.Asc77.AscC25V29

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Abstract

open MulAction Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_sylow {C : Subgroup G} (S : Sylow 2 G) (hSC : (S : Subgroup G) ≤ C)
    {n : G} (hnC : n ∈ C) {i : ℕ} (hn : orderOf n = 2 ^ i) :
    ∃ c ∈ C, c * n * c⁻¹ ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let n' : ↥C := ⟨n, hnC⟩
  have hn' : orderOf n' = 2 ^ i := by rw [← hn, ← Subgroup.orderOf_coe]
  have hA : IsPGroup 2 ↥(Subgroup.zpowers n') := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hn']
    exact ⟨i, rfl⟩
  obtain ⟨P, hP⟩ := hA.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C P (S.subtype hSC)
  refine ⟨(c : G), c.2, ?_⟩
  have h1 : n' ∈ (P : Subgroup ↥C) := hP (Subgroup.mem_zpowers n')
  have h2 : (c * n' * c⁻¹ : ↥C) ∈ ((c • P : Sylow 2 ↥C) : Subgroup ↥C) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨n', h1, rfl⟩
  rw [hc] at h2
  have h3 : (c * n' * c⁻¹ : ↥C) ∈ (S : Subgroup G).subgroupOf C := by
    simpa using h2
  exact Subgroup.mem_subgroupOf.mp h3


end Abstract

section Defs


end Defs

section Main


end Main

end CFSG.ClassicalInvolution.Asc77.C25V
