module

public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields

public section

namespace CFSG.ClassicalInvolution

open scoped MatrixGroups
open CFSG.ComponentClassification

variable {F : Type*} [Field F] [Finite F]

theorem outer_sl2_solvable (h4 : 4 ≤ Nat.card F) :
    Group.IsSolvable (OuterAutomorphisms.Outer SL(2, F)) := by
  have := sl2_isPerfect h4
  have : Group.IsSolvable
      (OuterAutomorphisms.Outer (SL(2, F) ⧸ Subgroup.center SL(2, F))) :=
    CatalogueSchreierLinearTwo.outer_solvable F
  exact OuterAutomorphisms.solvable_of_centerQuotient SL(2, F)

theorem perfect_action_inner_of_equiv_sl2 {P Q : Type*} [Group P] [Group.IsPerfect P] [Group Q]
    (h4 : 4 ≤ Nat.card F) (e : Q ≃* SL(2, F)) (ψ : P →* MulAut Q) (x : P) :
    ∃ q : Q, ψ x = MulAut.conj q := by
  have := outer_sl2_solvable (F := F) h4
  have : Group.IsSolvable (OuterAutomorphisms.Outer Q) :=
    OuterAutomorphisms.solvable_of_equiv e.symm
  exact OuterAutomorphisms.perfect_action_inner ψ x

theorem perfect_subgroup_le_range_conj (h4 : 4 ≤ Nat.card F)
    (H : Subgroup (MulAut SL(2, F))) [Group.IsPerfect H] :
    H ≤ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
  intro α hα
  obtain ⟨x, hx⟩ := perfect_action_inner_of_equiv_sl2 h4 (MulEquiv.refl SL(2, F)) H.subtype
    ⟨α, hα⟩
  exact ⟨x, hx.symm⟩


end CFSG.ClassicalInvolution
