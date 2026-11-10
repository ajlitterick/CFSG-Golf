module

public import CFSG.GH74.GLS.Stage2.Local.Closed
public import CFSG.GH74.GLS.Stage2.Local.P34Step1

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

@[expose] def Step23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ → HasTwoInvolutionClasses (HBar H) →
      IsSimpleGroup ↥(generalizedFitting (HBar H)) ∧
        (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) ∧ PerfInJ H


end CFSG.GH74.GLS.Stage2.Local.P34
