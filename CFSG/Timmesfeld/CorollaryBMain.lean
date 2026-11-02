module

public import CFSG.Timmesfeld.CorollaryBQuot
public import CFSG.Timmesfeld.CorollaryBOutcome
public import CFSG.Timmesfeld.CorollaryBZStar
public import CFSG.Timmesfeld.CorollaryBDegen
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Monster.Code.Weights
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Th.Max3.Involutions

public section

namespace CFSG.Timmesfeld.CorB

open Subgroup

variable {X : Type} [Group X] [Finite X] {t : X}

theorem main (h : Setup t) :
    (∃ K : Subgroup X, K ≤ normalClosure ({t} : Set X) ∧
        (K.subgroupOf (normalClosure ({t} : Set X))).Normal ∧ Odd (Nat.card K) ∧
        normalClosure ({t} : Set X) = K ⊔ zpowers t) ∨
      (∀ x ∈ normalClosure ({t} : Set X), ∀ y ∈ normalClosure ({t} : Set X),
        x * y = y * x ∧ x * x = 1) ∨
      ((∀ d ∈ cls t, ∀ e ∈ cls t, orderOf (d * e) ≠ 4) ∧
        CFSG.BenderSuzuki.IsBenderGroup
          (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X)))) ∨
      (Hyp (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X)))
          (QuotientGroup.mk' (center ↥(normalClosure ({t} : Set X))) '' clsIn t) ∧
        OutcomeTwo (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X)))
          (QuotientGroup.mk' (center ↥(normalClosure ({t} : Set X))) '' clsIn t)) := by
  by_cases hpair : ∃ τ ∈ conjCent t, τ ≠ t
  · by_cases hdeg : ∀ d ∈ cls t, ∀ e ∈ cls t, orderOf (d * e) ≠ 4
    · rcases h.degenerate hpair hdeg with h2 | hB
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl ⟨hdeg, hB⟩))
    · push Not at hdeg
      have hH := h.hyp_quotient hpair hdeg
      exact Or.inr (Or.inr (Or.inr ⟨hH, outcomeTwo_of_noOddCent hH (h.noOddCent_quotient hdeg)⟩))
  · push Not at hpair
    exact Or.inl (zStar_case h.orderOf_eq fun τ hτt hτ => hpair τ ⟨hτt, hτ⟩)

end CFSG.Timmesfeld.CorB
