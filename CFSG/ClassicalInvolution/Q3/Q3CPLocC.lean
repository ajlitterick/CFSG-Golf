module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3CPNbhd
public import CFSG.ClassicalInvolution.Q3.Q3CPTwin
public import CFSG.ClassicalInvolution.Q3.Q3YSFinal
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section Def

variable {G : Type} [Group G]

@[expose] def LocCommuteAt (K : Subgroup G) (_z : G) : Prop :=
  ∀ (L M : Subgroup G) (l m : G), L ∈ conjClass3 K → M ∈ conjClass3 K →
    IsClassicalMember3 L l → IsClassicalMember3 M m → l ≠ m → l * m = m * l →
    (∃ P : Subgroup G, IsSylow2In P M ∧ P ≤ Subgroup.centralizer ({l} : Set G)) → Commutes L M

variable {K : Subgroup G} {z : G}

theorem LocCommuteAt.of_le [Finite G] (h : LocCommuteAt K z) {L M : Subgroup G} {l m : G}
    (hL : L ∈ conjClass3 K) (hM : M ∈ conjClass3 K) (hl : IsClassicalMember3 L l)
    (hm : IsClassicalMember3 M m) (hne : l ≠ m) (hc : l * m = m * l)
    (hMc : M ≤ Subgroup.centralizer ({l} : Set G)) : Commutes L M := by
  obtain ⟨P, hP⟩ := exists_isSylow2In M
  exact h L M l m hL hM hl hm hne hc ⟨P, hP, hP.1.trans hMc⟩


end Def


section Twin


end Twin

section Nbhd


end Nbhd

end CFSG.ClassicalInvolution.Q3.Q3CP
