module

public import CFSG.ClassicalInvolution.Q3.Q3PWeak

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Vocabulary

variable {G : Type} [Group G]

abbrev conjClass3 (K : Subgroup G) : Set (Subgroup G) :=
  Set.range fun g : G => conjSub g K


@[expose] def BootData3 (Ω : Set (Subgroup G)) : Prop :=
  ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G), L₀ ∈ Ω ∧ IsClassicalMember3 L₀ z₀ ∧
    IsElemAbelian 2 A ∧ Nat.card A = 8 ∧ z₀ ∈ A ∧ L₀ ≤ Subgroup.centralizer (A : Set G)


@[expose] def Setup3 (K : Subgroup G) (z : G) : Prop :=
  ExactMembers3 (conjClass3 K) ∧ LocalOddCentral (conjClass3 K) {z}

end Vocabulary

section Branches


end Branches

end CFSG.ClassicalInvolution.Q3
