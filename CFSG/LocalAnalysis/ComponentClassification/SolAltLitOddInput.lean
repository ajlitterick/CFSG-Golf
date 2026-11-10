module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs

public section

namespace CFSG.ComponentClassification.SolAltLit

open CFSG Subgroup

@[expose] def SolomonAlternatingOddInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ¬ ∃ (x : X) (L : Subgroup X) (n : ℕ), orderOf x = 2 ∧ Odd n ∧ 9 ≤ n ∧
      L ≤ centralizer ({x} : Set X) ∧ IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n))


end CFSG.ComponentClassification.SolAltLit
