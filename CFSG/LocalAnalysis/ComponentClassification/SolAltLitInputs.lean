module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced

public section

namespace CFSG.ComponentClassification.SolAltLit

open CFSG Subgroup

@[expose] def IsAltTwoComponent {X : Type*} [Group X] (t : X) (K : Subgroup X) (n : ℕ) : Prop :=
  orderOf t = 2 ∧ K ≤ centralizer ({t} : Set X) ∧
    IsPComponent 2 (K.subgroupOf (centralizer ({t} : Set X))) ∧
    Nonempty (K ⧸ pPrimeCore 2 K ≃* alternatingGroup (Fin n))


end CFSG.ComponentClassification.SolAltLit
