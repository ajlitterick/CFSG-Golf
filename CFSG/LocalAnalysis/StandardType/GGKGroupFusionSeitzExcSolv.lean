module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSeitzExcUFourTwoInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 1 → d.1 = .twistedA 3 q →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ X : Subgroup K, X ≠ ⊤ → ¬ 3 ∣ X.index → Group.IsSolvable ↥X


end CFSG.StandardType
