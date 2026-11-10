module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

universe u v

variable {G : Type u} [Group G] [Finite G]


omit [Finite G] in
theorem original_restricted_stabilizer
    (H A : Subgroup G) (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ a ∈ A, ∀ omega ∈ Delta, pointRightCosetMul H omega a ∈ Delta)
    (omega : Delta) :
    letI := pointInvariantSetInverseRightAction H A Delta hstable
    MulAction.stabilizer A omega = (rightCosetStabilizer H omega.val).subgroupOf A := by
  let := pointInvariantSetInverseRightAction H A Delta hstable
  ext a
  rw [MulAction.mem_stabilizer_iff]
  change (⟨pointRightCosetMul H omega.val (a : G)⁻¹, _⟩ : Delta) = omega ↔
    (a : G) ∈ rightCosetStabilizer H omega.val
  rw [Subtype.ext_iff, ← mem_point_right_stabilizer_iff H omega.val (a : G)⁻¹]
  exact (rightCosetStabilizer H omega.val).inv_mem_iff


end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
