module

public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.Monster.B.TwoA.Amalgam.NativeChain
public import CFSG.Monster.B.CTIB.Rep4371Main

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.LieType.Chevalley.C2E6Std

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem centralizerInput_of_ambient
    (hamb : AmbientRootOrbitsHyp) : CentralizerInput :=
  (global_label_of_ambient hamb).2.2.2

theorem native_rank_1860_unique_component_of_ambient
    (hamb : AmbientRootOrbitsHyp) :
    ∀ s : Sbp, orderOf s = 2 → ((βr s) - 1).rank = 1860 →
      ∃ K : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K ∧
        (∀ K' : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K' → K' = K) ∧
        CFSG.IsQuasisimple K ∧ Nat.card (Subgroup.center K) = 2 ∧
        Nonempty (K ⧸ Subgroup.center K ≃* stdGroup) ∧
        Nat.card (K ⧸ Subgroup.center K) = 76532479683774853939200 ∧
        17 ∣ Nat.card (K ⧸ Subgroup.center K) :=
  native_rank_1860_unique_component (centralizerInput_of_ambient hamb)

end CFSG.Monster.B.CTIB
