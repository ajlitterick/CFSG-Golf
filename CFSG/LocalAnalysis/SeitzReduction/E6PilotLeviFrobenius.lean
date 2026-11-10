module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviBaseChange
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley (baseChangeGL)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem frob_frob_extension_two (z : FiniteField.Extension K 2 2) :
    FiniteField.Extension.frob K 2 2 (FiniteField.Extension.frob K 2 2 z) = z := by
  have := Fintype.ofFinite (FiniteField.Extension K 2 2)
  rw [← AlgEquiv.mul_apply, ← sq, FiniteField.Extension.frob_iterate_apply,
    ← FiniteField.natCard_extension K 2 2, ← Fintype.card_eq_nat_card]
  exact FiniteField.pow_card z


theorem exists_baseChangeGL_eq_of_mem_rootSpan_a5LeviRoots_frob
    {d : ModGL .E6 (FiniteField.Extension K 2 2)}
    (hd : d ∈ rootSpan .E6 (FiniteField.Extension K 2 2) a5LeviRoots)
    (hσd : baseChangeGL (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom d = d) :
    ∃ d₀ ∈ rootSpan .E6 K a5LeviRoots,
      baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) d₀ = d :=
  exists_baseChangeGL_eq_of_mem_rootSpan_a5LeviRoots _ _ (fun z => F4Pilot.frob_eq_self_iff z)
    frob_frob_extension_two hd hσd

end CFSG.SeitzReduction.E6Pilot
