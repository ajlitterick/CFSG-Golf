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

theorem recognition_exists_of_models
    (hmodels : ∀ (d₀ : NativeSporadic.B) (_ : orderOf d₀ = 2)
      (_ : Matrix.rank (d₀.val.val - 1) = 1860)
      (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
      (d : G) (_ : orderOf d = 2)
      (_ : Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
        Subgroup.centralizer ({d₀} : Set NativeSporadic.B))),
      Nonempty (G ≃* NativeSporadic.B)) :
    ∃ (B : Type) (_ : Group B) (_ : Finite B), IsSimpleGroup B ∧
      Nat.card B = CFSG.Open.sporadicOrderBabyMonster ∧
      ∃ d₀ : B, orderOf d₀ = 2 ∧
        Nat.card (Subgroup.centralizer ({d₀} : Set B)) =
          4 * CFSG.Open.sporadicOrderTwistedE6Two ∧
        ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
          ∀ d : G, orderOf d = 2 →
            Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
              Subgroup.centralizer ({d₀} : Set B)) →
            Nonempty (G ≃* B) :=
  ⟨NativeSporadic.B, inferInstance, inferInstance, CFSG.Sporadic.B.fam_b_simplicity,
    CFSG.Monster.Existence.card_nativeB, labelB, orderOf_labelB, natCard_centralizer_labelB,
    fun G _ _ hG d hd hc => @hmodels labelB orderOf_labelB rank_labelB G _ _ hG d hd hc⟩

end CFSG.Monster.B.GSide
