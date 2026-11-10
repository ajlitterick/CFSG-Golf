module

public import CFSG.Open.SporadicBabyMonsterRecognitionMilestoneDefs
public import CFSG.Monster.Existence.BabyOrder
public import CFSG.Monster.B.GSide.CompletionFusion

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.CTIB

@[expose] def labelB :
    NativeSporadic.B := iotaEquiv.symm labelS

theorem orderOf_labelS :
    orderOf labelS = 2 := by
  have h : orderOf (sEquiv labelS) = orderOf labelS := MulEquiv.orderOf_eq sEquiv _
  rw [sEquiv_labelS_eq_cV0, orderOf_coe_cV0] at h
  exact h.symm

theorem orderOf_labelB :
    orderOf labelB = 2 := by
  have h : orderOf (iotaEquiv.symm labelS) = orderOf labelS := by
    with_reducible_and_instances exact MulEquiv.orderOf_eq iotaEquiv.symm _
  exact h.trans orderOf_labelS

theorem rank_labelB :
    Matrix.rank (labelB.val.val - 1) = 1860 :=
  (rank_iotaEquiv_symm labelS).trans rank_labelS

theorem natCard_centralizer_labelS :
    Nat.card (Subgroup.centralizer {labelS}) = 306129918735099415756800 := by
  have h := Nat.card_congr (centralizerEquiv sEquiv labelS).toEquiv
  rw [sEquiv_labelS_eq_cV0, natCard_centralizer_cV0] at h
  exact h

theorem natCard_centralizer_labelB :
    Nat.card (Subgroup.centralizer ({labelB} : Set NativeSporadic.B)) =
      4 * CFSG.Open.sporadicOrderTwistedE6Two := by
  have e : Subgroup.centralizer {labelS} ≃*
      Subgroup.centralizer ({iotaEquiv.symm labelS} : Set NativeSporadic.B) := by
    with_reducible_and_instances exact centralizerEquiv iotaEquiv.symm labelS
  have h := (Nat.card_congr e.toEquiv).symm.trans natCard_centralizer_labelS
  exact h.trans (by norm_num [CFSG.Open.sporadicOrderTwistedE6Two])


end CFSG.Monster.B.GSide
