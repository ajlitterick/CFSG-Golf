module

public import CFSG.ClassicalInvolution.Balance.ToralBalanceLie
public import CFSG.ClassicalInvolution.Balance.ToralBalanceWeakFrame
import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.Assembly.LowTwoRank

@[expose] def IsOddLieComponent {X : Type} [Group X] (L : Subgroup X) : Prop :=
  ∃ (t : StatedLieTag) (n p f : ℕ), p ≠ 2 ∧ (t = .PSL → 3 ≤ n) ∧
    (t ∈ classicalTags ∨ t ∈ chevalleyExceptionalTags) ∧
    LieModel (↥L ⧸ Subgroup.center ↥L) t n p f

theorem involutionCentralizerB_of_isOddLieComponent {X : Type} [Group X] [Finite X]
    {L : Subgroup X} (hL : CFSG.Open.IsQuasisimple ↥L) (h : IsOddLieComponent L) :
    InvolutionCentralizerB L := by
  obtain ⟨t, n, p, f, hp, hn, ht, hmodel⟩ := h
  exact involutionCentralizerB_of_lieModel hL hp hn ht hmodel

theorem isOddLieComponent_of_surjective {X : Type} [Group X] {L : Subgroup X} {K : Type}
    [Group K] (hK : CFSG.Open.IsQuasisimple K) (ψ : K →* ↥L) (hψ : Function.Surjective ψ)
    (hψ1 : ∃ x, ψ x ≠ 1) {t : StatedLieTag} {n p f : ℕ} (hp : p ≠ 2) (hn : t = .PSL → 3 ≤ n)
    (ht : t ∈ classicalTags ∨ t ∈ chevalleyExceptionalTags)
    (hmodel : LieModel (K ⧸ Subgroup.center K) t n p f) : IsOddLieComponent L := by
  have hK' : CFSG.IsQuasisimple K := CatalogueBAlternating.quasisimple_iff_native.mpr hK
  exact ⟨t, n, p, f, hp, hn, ht, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hK' hψ
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hK' hψ1)) hmodel⟩

section Frame


end Frame

section WeakFrame


end WeakFrame

end CFSG.ClassicalInvolution.Balance
