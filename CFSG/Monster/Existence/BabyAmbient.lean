module

public import CFSG.Monster.Existence.BabyTableIIIOf
public import CFSG.Monster.B.CTIB.UniqueComponentAmbient
public import CFSG.Monster.B.CTIB.Rank2158Final
public import CFSG.Monster.B.CTIB.DistThreeProductFinal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.GMS CFSG.Blueprint

theorem centralizerInput_B :
    CTIB.CentralizerInput :=
  CTIB.centralizerInput_of_ambient TwoA.Amalgam.ambientRootOrbitsHyp

theorem twoPointShape_one_MGriess :
    TwoPointShape (cent2 tGriess uGriess) 1 :=
  twoPointShape_one_of_centralizerInput centralizerInput_B

theorem natCard_centralizer_rep_one :
    Nat.card ↥(Subgroup.centralizer ({babyRep 1} : Set NativeSporadic.B)) = babyCentOrder 0 :=
  natCard_centralizer_rep_one_of centralizerInput_B

theorem natCard_centralizer_rep_five :
    Nat.card ↥(Subgroup.centralizer ({babyRep 5} : Set NativeSporadic.B)) = babyCentOrder 3 := by
  obtain ⟨⟨v, u, hvu, hc⟩, -⟩ := CTIB.native_rank_2158_distance_three_product_final
  have hC := (CTIB.distance_three_product_full_centralizer_final hvu rfl rfl rfl).2.2.2.2.2.1
  have e1 := Nat.card_congr
    (@CTIB.centralizerEquiv NativeSporadic.B Sbp Units.instGroup _ CTIB.iotaEquiv
      (babyRep 5)).toEquiv
  rw [babyRep, MulEquiv.apply_symm_apply] at e1
  have e2 := Nat.card_congr (CTIB.centralizerEquiv CTIB.sEquiv (CTIB.rs 5)).toEquiv
  rw [babyRep, e1, e2, natCard_centralizer_eq_of_isConj hc, hC]
  norm_num [babyCentOrder]

theorem babyTableIII_of_rep_three
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) = babyCentOrder 2) :
    BabyTableIII :=
  babyTableIII_of centralizerInput_B h3 natCard_centralizer_rep_five

end CFSG.Monster.Existence
