module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL3Wr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_noncyclic_seven_fix {M V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : M ≤ stabTil V₀ V) (hrank : 3 ≤ CFSG.Open.pRank 7 M)
    (hT : (tensorPairModel SL32 SL32).RealizesMod (barSub V₀ V hV L))
    (hnorm : Mbar M V₀ V hV ≤
      normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))) :
    ∃ B : Subgroup G, B ≤ M ∧ IsPGroup 7 B ∧ ¬ IsCyclic B ∧
      3 ≤ rk ↥(fixV (barSub V₀ V hV B)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (by norm_num : Nat.Prime 7) hrank
  have hEst : E ≤ stabTil V₀ V := hEM.trans hMs
  have hEbel : IsElemAbelian 7 (barSub V₀ V hV E) :=
    (hEel.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)
  have hEbN : barSub V₀ V hV E ≤
      normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (barSub_mono V₀ V hV hEM).trans hnorm
  obtain ⟨Q, hQE, hcard, hfix⟩ := exists_sub_of_isPGroup_seven hT hEbN hEbel.isPGroup
  have hid := s16c7_card_mul_card_preBarSub hV hEst hQE
  have hBE : preBarSub E V₀ V hV Q ≤ E := inf_le_left
  have hB49 : 49 ≤ Nat.card (preBarSub E V₀ V hV Q) := by
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    rw [hEcard] at hid
    by_contra hlt
    have hle : Nat.card (preBarSub E V₀ V hV Q) ≤ 48 := by omega
    nlinarith [Nat.mul_le_mul hle hcard]
  have hBel : IsElemAbelian 7 (preBarSub E V₀ V hV Q) := hEel.mono hBE
  have hbar : barSub V₀ V hV (preBarSub E V₀ V hV Q) = Q := by
    rw [barSub_preBarSub]
    exact inf_eq_left.2 hQE
  refine ⟨preBarSub E V₀ V hV Q, hBE.trans hEM, hBel.isPGroup, ?_, ?_⟩
  · refine s16c7_not_isCyclic_of_elemAbelian (by norm_num) hBel ?_
    omega
  · rw [hbar]
    have hsq := s15_Infra_vtil_sq_eq_one V₀ V hV
    have h8 : Nat.card ↥(fixV Q) = 2 ^ rk ↥(fixV Q) := card_eq_two_pow hsq (fixV Q)
    rw [h8] at hfix
    by_contra hlt
    have : rk ↥(fixV Q) ≤ 2 := by omega
    have : 2 ^ rk ↥(fixV Q) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
