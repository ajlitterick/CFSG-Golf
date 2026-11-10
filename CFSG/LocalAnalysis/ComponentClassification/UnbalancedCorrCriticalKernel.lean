module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrKernelCases
public import CFSG.LieType.Simplicity.Basic
import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCritical
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrKernelQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrMaximalTriple

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open CFSG.ComponentClassification.UnbalancedLayer (GSUnbalancingTriple)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem fusionZStar_eq_pPrimeCore_of_isSimpleGroup {Y : Type*} [Group Y]
    (hs : IsSimpleGroup (Y ⧸ pPrimeCore 2 Y)) (hna : ∃ u v : Y ⧸ pPrimeCore 2 Y, u * v ≠ v * u) :
    CFSG.Open.fusionZStar Y = pPrimeCore 2 Y := by
  have hO := UnbalancingLocal.fusionOddCore_eq_pPrimeCore Y
  have hc : center (Y ⧸ pPrimeCore 2 Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Y ⧸ pPrimeCore 2 Y)) with h | h
    · exact h
    · exfalso
      obtain ⟨u, v, huv⟩ := hna
      have hu : u ∈ center (Y ⧸ pPrimeCore 2 Y) := by rw [h]; exact mem_top u
      exact huv (mem_center_iff.mp hu v).symm
  let e : Y ⧸ CFSG.Open.fusionOddCore Y ≃* Y ⧸ pPrimeCore 2 Y :=
    QuotientGroup.quotientMulEquivOfEq hO
  ext x
  constructor
  · intro hx
    have h1 : QuotientGroup.mk' (CFSG.Open.fusionOddCore Y) x ∈
        center (Y ⧸ CFSG.Open.fusionOddCore Y) := hx
    have h2 : e (QuotientGroup.mk' _ x) ∈ center (Y ⧸ pPrimeCore 2 Y) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, mem_center_iff.mp h1 g']
    rw [hc, mem_bot] at h2
    have h3 : (x : Y ⧸ pPrimeCore 2 Y) = 1 := by
      rw [← h2]
      exact (QuotientGroup.quotientMulEquivOfEq_mk hO x).symm
    exact (QuotientGroup.eq_one_iff x).mp h3
  · intro hx
    have h1 : x ∈ CFSG.Open.fusionOddCore Y := by rw [hO]; exact hx
    show QuotientGroup.mk' (CFSG.Open.fusionOddCore Y) x ∈ center _
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr h1]
    exact one_mem _

omit [Finite G] in
theorem isSimpleGroup_of_statedClassicalModel_psl_two {Y : Type} [Group Y] {p f : ℕ}
    (hm : StatedClassicalModel Y .PSL 2 p f) : IsSimpleGroup Y :=
  CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hm


end CFSG.ComponentClassification.UnbalancedCorr
