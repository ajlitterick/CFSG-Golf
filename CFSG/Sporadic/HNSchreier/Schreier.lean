module

public import CFSG.Sporadic.HNSchreier.FullAut

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.ComponentClassification.OuterAutomorphisms

instance outer_HN_isCyclic :
    IsCyclic (Outer Blueprint.NativeSporadic.HN) :=
  ctuc_hn_full_automorphism_group.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ctuc_hn_Schreier :
    Group.IsSolvable (Outer Blueprint.NativeSporadic.HN) ∧
    IsCyclic (Outer Blueprint.NativeSporadic.HN) ∧
    Nat.card (Outer Blueprint.NativeSporadic.HN) = 2 ∧
    Subgroup.zpowers (QuotientGroup.mk hnOuterC : Outer Blueprint.NativeSporadic.HN) = ⊤ :=
  ⟨inferInstance, outer_HN_isCyclic, card_outer_HN, outer_HN_zpowers⟩

theorem AT_HN_Schreier :
    Group.IsSolvable (Outer Blueprint.NativeSporadic.HN) :=
  ctuc_hn_Schreier.1

end CFSG.Sporadic.HNSchreier
