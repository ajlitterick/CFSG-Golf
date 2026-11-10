module

public import CFSG.LocalAnalysis.LargeEvenClassification.PrimeComplementCore

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse


theorem commutator_le_of_normalized {Ambient : Type groupUniverse} [Group Ambient]
    (Invariant Acting : Subgroup Ambient)
    (hnormalizes : Acting ≤ Subgroup.normalizer (Invariant : Set Ambient)) :
    ⁅Invariant, Acting⁆ ≤ Invariant := by
  apply Subgroup.commutator_le.mpr
  intro element helement conjugator hconjugator
  rw [commutatorElement_def]
  have hconjugate := (Subgroup.mem_normalizer_iff.mp (hnormalizes hconjugator)
    element⁻¹).mp (Invariant.inv_mem helement)
  simpa only [mul_assoc] using Invariant.mul_mem helement hconjugate


end CFSG.LargeEvenClassification.Helpers
