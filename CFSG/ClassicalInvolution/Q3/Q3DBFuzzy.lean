module

public import CFSG.ClassicalInvolution.Q3.Q3DBEdge
public import CFSG.ClassicalInvolution.Q3.Q3NLExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3DB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement


section Adjacency

variable {G : Type} [Group G]


end Adjacency

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem actsTrivOnQuot_of_mem_omegaNbr (hK : IsClassicalMember3 K z)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M N : Subgroup G}
    (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a : G} (ha : IsClassicalMember3 M a) :
    ActsTrivOnQuot N a := by
  obtain ⟨h1, h2⟩ := fuzzy_of_mem_omegaNbr hK hint hN ha
  exact ⟨mem_normalizer_iff_conjSub_eq.mpr h1, h2⟩


theorem mem_tqMembers3_of_mem_omegaNbr (hK : IsClassicalMember3 K z)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M N : Subgroup G}
    (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a : G} (ha : IsClassicalMember3 M a) :
    N ∈ Q3NL.tqMembers3 (CoreAssembly.conjClass K) a :=
  ⟨hN.1, mem_trivialOnQuot_iff_actsTrivOnQuot.mpr (actsTrivOnQuot_of_mem_omegaNbr hK hint hN ha)⟩

end CFSG.ClassicalInvolution.Q3.Q3DB
