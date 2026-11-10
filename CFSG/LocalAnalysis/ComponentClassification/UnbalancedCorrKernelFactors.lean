module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrKernelTools
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerIsoCorrSylowGrowth

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]


theorem isSimpleGroup_of_isQuasisimple_of_center_eq_bot {Q : Type*} [Group Q]
    (hQ : IsQuasisimple Q) (hZ : center Q = ⊥) : IsSimpleGroup Q := by
  have := hQ.2.1
  exact ((QuotientGroup.quotientBot (G := Q)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).isSimpleGroup

theorem exists_ne_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ∃ u v : Q, u * v ≠ v * u := by
  obtain ⟨u, v, huv⟩ := hQ.2.2
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center Q) u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
  refine ⟨u, v, fun h => huv ?_⟩
  rw [← map_mul, ← map_mul, h]


end CFSG.ComponentClassification.UnbalancedCorr
