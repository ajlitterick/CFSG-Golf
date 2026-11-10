module

public import CFSG.ClassicalInvolution.Balance.PassTwo
public import CFSG.ClassicalInvolution.Generic.InductionLocal

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

@[expose] def InCommonComponent (x : G) (K L : Subgroup G) : Prop :=
  ∃ Q : Subgroup (OddQuot x), CFSG.IsComponent Q ∧ modOdd x K ≤ Q ∧ modOdd x L ≤ Q


omit [Finite G] in
theorem commutator_subgroupOf_eq_top {C K : Subgroup G} (hKC : K ≤ C) (hK : Group.IsPerfect ↥K) :
    commutator ↥(K.subgroupOf C) = ⊤ := by
  have : Group.IsPerfect ↥(K.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKC).symm.surjective
  exact Group.IsPerfect.commutator_eq_top


@[expose] def Stage2 (Ω : Set (Subgroup G)) (X₂ : Set G) : Prop :=
  ExactMembers Ω ∧ ∀ x ∈ X₂, LocalOddCentral Ω {x}


end CFSG.ClassicalInvolution.Balance
