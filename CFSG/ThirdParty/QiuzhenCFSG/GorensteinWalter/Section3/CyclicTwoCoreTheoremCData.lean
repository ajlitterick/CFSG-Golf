module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCyclicTwoCoreInfra
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Strict conditional reduction for the five Theorem-C A₇-model inputs

The paper's remaining source paragraph (after `B ⊆ M`, p. 223) derives the
five inputs of `firstCase_cyclicTwoCore_impossible_of_a7model` from:

1. the normalizer-control statement
   `firstCase_cyclic_normalizer_le_M_of_le_B_inter_M`
   (nontrivial subgroups of `B ∩ M` have ambient normalizer inside `M`;
   this is now supplied unconditionally by
   `firstCase_cyclic_componentLayer_normalizer_eq_of_a7` together with
   `firstCase_cyclic_normalizer_le_M_of_le_B_inter_M_of_componentLayer_eq`),
2. the centralizer decompositions `C_U(t₁) = B × P₀` and `C_U(t₂) = B`,
3. the oriented-prime conclusion `od.p = 3`.

The normalizer-control leg is now landed.  The two centralizer
decompositions reduce to the remaining algebraic core `C_B(P) ≠ 1`:
`CyclicTwoCoreCentralizerT1.firstCase_cyclic_primeCore_le_M_of_a7_of_CB_ne`
then gives `P = O₃(U) ≤ M`, from which the decompositions and the five
inputs follow as recorded on `tasks/gw-section3.md`.  This module keeps the
strict conditional reduction as the landing surface until that final
centralizer-core lemma is proved.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The five Theorem-C A₇-model inputs required by
`firstCase_cyclicTwoCore_impossible_of_a7model`, packaged as one predicate
for the strict conditional reduction. -/
@[expose] public def firstCase_cyclic_a7_theoremC_data
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c) : Prop :=
  (od.d.bg.B1 ⊓
    @BenderGlauberman.Hyp11.K2 G _ _ od.d.bg
      (firstCaseBGKData hmin c od.d) = qCoreOf od.d.bg.U 3) ∧
    (@BenderGlauberman.Hyp11.K G _ _ od.d.bg
        (firstCaseBGKData hmin c od.d) =
      ((pPrimeCore 3 (fittingSubgroup od.d.bg.U)).map
        (fittingSubgroup od.d.bg.U).subtype).map od.d.bg.U.subtype) ∧
    (qCoreOf od.d.bg.U 3 ≤ Subgroup.centralizer
      (od.d.bg.B : Set G)) ∧
    (@BenderGlauberman.Hyp11.K G _ _ od.d.bg
        (firstCaseBGKData hmin c od.d) ≠ ⊥) ∧
    (∀ b : G, b ∈ od.d.bg.B → b ≠ 1 → ∀ k : G,
      k ∈ ((pPrimeCore 3 (fittingSubgroup od.d.bg.U)).map
        (fittingSubgroup od.d.bg.U).subtype).map od.d.bg.U.subtype →
        k ≠ 1 → b * k * b⁻¹ ≠ k)


end CFSG.GorensteinWalter
