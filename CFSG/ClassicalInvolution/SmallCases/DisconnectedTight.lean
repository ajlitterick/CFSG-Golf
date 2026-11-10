module

public import CFSG.ClassicalInvolution.SmallCases.Rank3NormalEight
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedStatements
public import CFSG.ClassicalInvolution.TwoGroupCase.Packets
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.DisconnectedInvolutionGraph.Helpers

section TwoGenerators


end TwoGenerators

section Count

variable {G : Type*} [Group G] [Finite G]


end Count


section Tight

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_normalizer_of_mem_centralizer {K : Subgroup G} {z : G}
    (hKC : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal) {s : G}
    (hs : s ∈ Subgroup.centralizer ({z} : Set G)) : s ∈ Subgroup.normalizer (K : Set G) := by
  have key : ∀ t ∈ Subgroup.centralizer ({z} : Set G), ∀ k ∈ K, t * k * t⁻¹ ∈ K := by
    intro t ht k hk
    have h := hKn.conj_mem ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨t, ht⟩
    exact Subgroup.mem_subgroupOf.mp h
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact key s hs k
  · intro hk
    have := key s⁻¹ (inv_mem hs) _ hk
    simpa [mul_assoc] using this


end Tight

section Assembly


end Assembly

end CFSG.ClassicalInvolution
