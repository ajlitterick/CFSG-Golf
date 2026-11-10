module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverSmall
import CFSG.LocalAnalysis.ComponentClassification.TBLitPSLCover
import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.J2
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Subgroup
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels
  GriessMultipliersCentralCovers)
open CFSG.GH74.Generic (card_center_dvd_hopfMultiplier centralQuotientMap
  centralQuotientMap_surjective centralQuotientMap_ker)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.LocalAnalysis.ComponentInitial (alternating_perfect_central_two_kernel_order_at_most_two
  PSL2_four_alternating_five_model PSL3_two_PSL2_seven_paired_isomorphism)

@[expose] def sporadicMultiplierOrder : TauCeti.SporadicName → ℕ
  | .M12 => 2 | .M22 => 12 | .J2 => 2 | .J3 => 3 | .HS => 2 | .McL => 3 | .Suz => 6
  | .Ru => 2 | .ONan => 3 | .Co1 => 2 | .Fi22 => 6 | .Fi24Prime => 3 | .B => 2 | _ => 1

@[expose] def SporadicMultipliers : Prop :=
  (∀ s : TauCeti.SporadicName, Nat.card (hopfMultiplier (Spor s)) = sporadicMultiplierOrder s) ∧
    Nat.card (hopfMultiplier NativeSporadic.ON) = 3

@[expose] def NoRankThreeDoubleCover (X : Type) [Group X] : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → Nat.card (center J) = 2 →
    Nonempty (J ⧸ center J ≃* X) → CFSG.pRank 2 J ≠ 3

@[expose] def NoRankThreeTwoCover (X : Type) [Group X] : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsTwoCover J X → CFSG.pRank 2 J ≠ 3

structure TwoCoverRanks : Prop where
  alternating : ∀ n : ℕ, 6 ≤ n → n ≤ 12 → NoRankThreeDoubleCover (alternatingGroup (Fin n))
  hs : NoRankThreeDoubleCover (Spor .HS)
  ru : NoRankThreeDoubleCover (Spor .Ru)
  m22 : NoRankThreeDoubleCover (Spor .M22)
  suz : 3 < CFSG.pRank 3 (Spor .Suz)
  psu42 : NoRankThreeDoubleCover (projSU 4 2 1)
  psl34 : ∀ (J : Type) [Group J] [Finite J], IsTwoCover J (projSL 3 (GaloisField 2 2)) →
    CFSG.pRank 2 J = 3 → IsCyclic (center J) ∧ Nat.card (center J) = 4
  g24 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
    q.exponent = 2 → NoRankThreeDoubleCover (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  sz8 : ∀ hm : (TauCeti.LieTypeIndex.suzuki 1).Valid,
    NoRankThreeTwoCover (TauCeti.CFSGIndex.lie ⟨.suzuki 1, hm⟩).Group
  sp62 : NoRankThreeDoubleCover (projSp 3 (GaloisField 2 1))
  omegaPlus : 3 < CFSG.pRank 3 (projOmegaPlus 4 (GaloisField 2 1))
  f42 : 3 < CFSG.pRank 3 (TauCeti.CFSGIndex.lie f4TwoIndex).Group

theorem odd_tableOrder_psl_two_even {n : ℕ} (hn : 3 ≤ n) : Odd (tableOrder .PSL 2 2 n) := by
  refine odd_tableOrder (odd_gcd_of_odd_right (odd_two_pow_sub_one (by omega))) odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_psl_three_even {n : ℕ} (hn : 3 ≤ n) : Odd (tableOrder .PSL 3 2 n) := by
  refine odd_tableOrder (odd_gcd_of_odd_right (odd_two_pow_sub_one (by omega))) odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_psp_two_even {n : ℕ} (hn : 1 ≤ n) : Odd (tableOrder .PSp 2 2 n) := by
  refine odd_tableOrder (odd_gcd_of_odd_right (odd_two_pow_sub_one hn)) odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_psu_four_even {n : ℕ} (hn : 2 ≤ n) : Odd (tableOrder .PSU 4 2 n) := by
  refine odd_tableOrder (odd_gcd_of_odd_right (odd_two_pow_add_one (by omega))) odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_g2_even {f : ℕ} (hf : 3 ≤ f) : Odd (tableOrder .G2 0 2 f) := by
  refine odd_tableOrder odd_one odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_suzuki {m : ℕ} (hm : 2 ≤ m) :
    Odd (tableOrder .twistedB2 0 2 (2 * m + 1)) := by
  refine odd_tableOrder odd_one odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem odd_tableOrder_ree_f4 (m : ℕ) : Odd (tableOrder .twistedF4 0 2 (2 * m + 1)) := by
  refine odd_tableOrder odd_one odd_one ?_
  unfold exceptionalOrders
  split <;> simp_all

theorem pRank_two_le_of_psl_two (hGA : GriessMultipliersAllModels)
    (hGC : GriessMultipliersCentralCovers) {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (hZ2 : IsPGroup 2 (center J)) (hZnt : Nontrivial (center J)) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : CFSG.Blueprint.LieModel (J ⧸ center J) .PSL 2 p f) :
    CFSG.pRank 2 J ≤ 1 := by
  obtain ⟨-, _, ⟨g⟩⟩ := CFSG.ComponentClassification.TBLit.psl_two_double_cover hGA hGC hq
    hZ2 ((Subgroup.nontrivial_iff_ne_bot _).mp hZnt) hp hp2 hm
  have h2F : (2 : GaloisField p f) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p f) p]; exact hp2)
  have : Finite (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p f)) :=
    Finite.of_equiv _ g.toEquiv
  rw [pRank_congr_mulEquiv one_lt_two g]
  exact pRank_two_SL2_le h2F

theorem lieModel_psl_two_five_of_alternating {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : CFSG.Blueprint.LieModel X .PSL 2 5 1 := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 5 1) (Or.inr (by rw [hK, pow_one]))
  have hadm : StatedLieAdmissible .PSL 2 5 1 := ⟨by norm_num, le_rfl, by decide⟩
  exact Or.inl ⟨by decide, hadm, GaloisField 5 1, inferInstance, inferInstance, hK,
    ⟨e.trans e5.symm⟩⟩


end CFSG.RankThree.PartTwo.Sec4.Census
