module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi22Row
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.AutModelTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterTransferRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.M12Cover CFSG.Monster.B.Fischer CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.Fi22

theorem fi22_card_fix_involutive
    (σ : MulAut ↥fi22P) (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Nat.card (fixSubgroup σ) = 1769472 ∨ Nat.card (fixSubgroup σ) = 53084160 ∨
      Nat.card (fixSubgroup σ) = 18393661440 ∨ Nat.card (fixSubgroup σ) = 3317760 ∨
      Nat.card (fixSubgroup σ) = 1045094400 ∨ Nat.card (fixSubgroup σ) = 2903040 := by
  have h := fi22_autModel
  have hw := h.elt_mem σ
  have hsp := h.elt_spec σ
  have hww : h.elt σ * h.elt σ = 1 := by
    have := congrArg h.hom hσ
    rwa [map_mul, map_one] at this
  have hw1 : h.elt σ ≠ 1 := by
    intro e
    apply hσ1
    refine MulEquiv.ext fun p => Subtype.ext ?_
    rw [hsp, e]
    simp
  have hw2 : orderOf (h.elt σ) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
  rw [card_fixSubgroup_eq hsp]
  by_cases hwP : h.elt σ ∈ fi22P
  · rcases card_centralizerIn_fi22_inner hwP hw2 with h1 | h1 | h1 <;> simp [h1]
  · rcases card_centralizerIn_fi22_outer hw hwP hw2 with h1 | h1 | h1 <;> simp [h1]

theorem fi22_autCenterCond2_native :
    AutCenterCond2 ↥fi22P := by
  intro ν σ hν hσ hνσ hfix
  rcases fi22_autCenterCondExc_native ν σ hν hσ hνσ hfix with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · by_cases hσ1 : σ = 1
    · exact Or.inl hσ1
    · refine Or.inr (Or.inr fun hTC => ?_)
      have hdvd : 2903040 ∣ Nat.card (fixSubgroup σ) := by
        rw [← h1]
        exact Subgroup.card_dvd_of_le fun y hy => hfix y hy
      have hP : 2 ^ (Nat.card ↥fi22P).factorization 2 = 2 ^ 17 :=
        two_pow_factorization_eq (b := 492567075) (by rw [card_fi22P]; norm_num) (by decide)
      rw [TwoCentralAut, hP] at hTC
      rcases fi22_card_fix_involutive σ hσ hσ1 with h | h | h | h | h | h <;>
        rw [h] at hdvd hTC <;> omega

theorem fi22_outTwo_native :
    OutTwo ↥fi22P :=
  fi22_autRowData.outTwo

theorem fi22_card_inf_centralizer
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsSporadic L .Fi22) {u : G}
    (hu : u ∈ L) (hu2 : orderOf u = 2) :
    Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 1769472 ∨
      Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 53084160 ∨
      Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 18393661440 := by
  obtain ⟨e⟩ := hL
  set E : ↥L ≃* ↥fi22P := e.trans fi22PermEquiv with hE
  set u' : ↥L := ⟨u, hu⟩ with hu'
  have h1 : Nat.card ↥(L ⊓ centralizer ({u} : Set G)) =
      Nat.card ↥(centralizerIn fi22P ((E u' : fi22P) : Equiv.Perm (Fin 3510))) :=
    calc Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = Nat.card ↥(centralizerIn L (u' : G)) := rfl
      _ = Nat.card (centralizer ({u'} : Set L)) :=
        (Nat.card_congr (centralizerSubgroupEquiv L u').toEquiv).symm
      _ = Nat.card (centralizer ({E u'} : Set fi22P)) :=
        Nat.card_congr (centralizerEquiv E u').toEquiv
      _ = _ := Nat.card_congr (centralizerSubgroupEquiv fi22P (E u')).toEquiv
  rw [h1]
  exact card_centralizerIn_fi22_inner (E u').2 (by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hu', Subgroup.orderOf_mk]
    exact hu2)


theorem fi22_autCenterCond2_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .Fi22) : AutCenterCond2 Y := by
  obtain ⟨e⟩ := h
  exact AutCenterCond2.of_mulEquiv (e.trans fi22PermEquiv).symm fi22_autCenterCond2_native

theorem fi22_outTwo_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .Fi22) : OutTwo Y := by
  obtain ⟨e⟩ := h
  exact OutTwo.of_mulEquiv (e.trans fi22PermEquiv).symm fi22_outTwo_native


end CFSG.EvenSporadicStandard.Solomon78
