module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeSelection
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem trivial_pair_intersection_centralizes_flip
    (H : Subgroup G) (a b : pointRightCosetSpace H)
    (t v : G) (ht : orderOf t = 2) (hflip : pointRightCosetMul H a t = b)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({v} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({v} : Set G))).Normal)
    (htL : t ∈ L)
    (hbot : L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) = ⊥) :
    (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) ⊓
      Subgroup.centralizer ({v} : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
  obtain ⟨_, _, horbit⟩ := pair_hull_orbit_premises H a b t v ht hflip
    L hLC hLnormal htL
  intro e he
  have heq : rightConjugateElem t e * t = 1 :=
    Subgroup.mem_bot.mp (hbot ▸ horbit e he)
  have hright : rightConjugateElem t e = t := by
    have heqt := mul_eq_one_iff_eq_inv.mp heq
    rwa [inv_eq_self_of_orderOf_eq_two ht] at heqt
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  change e⁻¹ * t * e = t at hright
  have he' := congrArg (fun s : G => e * s) hright
  simpa only [mul_assoc, mul_inv_cancel_left] using he'.symm


end CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
