module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyClass
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyEdge

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Theorem5
  (MemberAdj FuzzyMemberConn FuzzyEdgeInFrame FuzzyVertexConn fuzzyVertexConn_of_adj conjMembers
    commuteAdj fuzzyMemberConn_conjMembers)
open scoped commutatorElement

section Adjacency

@[expose] def ActsTrivOnQuot {H : Type} [Group H] (J : Subgroup H) (a : H) : Prop :=
  a ∈ Subgroup.normalizer (J : Set H) ∧ ∀ x ∈ J, ⁅a, x⁆ ∈ oddCoreIn J

theorem mem_trivialOnQuot_iff_actsTrivOnQuot {H : Type} [Group H] [Finite H]
    {J : Subgroup H} {a : H} :
    a ∈ trivialOnQuot J ↔ ActsTrivOnQuot J a :=
  mem_trivialOnQuot_iff

@[expose] def tqAdj (p f : ℕ) [Fact p.Prime] : MemberAdj :=
  fun {H} _ M N => ∃ a u : H, IsClassicalMember p f M a ∧ IsClassicalMember p f N u ∧
    ActsTrivOnQuot M u ∧ ActsTrivOnQuot N a

end Adjacency

section Member


end Member

end CFSG.ClassicalInvolution.Balance.Bootstrap
