module

public import CFSG.GH74.Uniqueness.Section7Prop74A
public import CFSG.GH74.Uniqueness.Section7Prop74B

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.prop74
    (S : ZDSetup X Z M) (hL73 : Lemma73Stmt Z M) {z : X} {p : ℕ}
    {W : Subgroup X} (hW : T4Max Z M z p W) :
    ∃ Γ : Set (Subgroup X), Prop74Spec Z M z W Γ := by
  by_cases hC : centralizer (CFSG.OddInversion.invertedSet W z : Set X) ≤ M
  · exact ⟨_, S.prop74_of_centralizer_le hL73 hW hC⟩
  · exact S.prop74_of_not_centralizer_le hW.cand hC


end CFSG.GH74.Uniqueness
