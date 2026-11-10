module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.Fi24PrimeAux.AutModel
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicGtFiveRowsAux.Fi24Seven
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven
import Certificates.Kernel.Misc.E6StdSlp
import Certificates.Kernel.KDense.Y443
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenEbarData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenEbarData
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporB
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporSuz
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporTh
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Sporadic.Fi24 (R JR)

theorem exists_plane_witness_of_oPrimeCoreTrivialAt {p : ℕ} (hp : p.Prime) {S : Type*} [Group S]
    (h : OPrimeCoreTrivialAt p S) {E : Subgroup S} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) :
    ∃ d ∈ E, d ≠ 1 ∧ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set S)) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hdE, hd1⟩ : ∃ d ∈ E, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rw [(Subgroup.eq_bot_iff_forall E).2 hcon, Subgroup.card_bot] at hEc
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  exact ⟨d, hdE, hd1, h d (orderOf_eq_prime (hE.2 d hdE) hd1)⟩

section MThirteen

theorem sporadicTwoPairHolds_M_thirteen : SporadicTwoPairHolds .M 13 := by
  rintro S _ _ _ hnab ⟨e⟩
  have hinn : innerAut S = ⊤ :=
    Subgroup.index_eq_one.mp (CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple e)
  exact isLocallyBalancedAbs_two_of_plane_witness (center_eq_bot_of_isSimpleGroup hnab) hinn
    fun E hE hEc => exists_plane_witness_of_oPrimeCoreTrivialAt (by norm_num)
      (sporadicOPrimeHolds_M_thirteen_of bThirteenOddCore_holds S ⟨e⟩) hE hEc

end MThirteen

section Fi24Seven

theorem sporadicTwoPairHolds_Fi24Prime_seven : SporadicTwoPairHolds .Fi24Prime 7 := by
  rintro S _ _ _ hnab ⟨e⟩
  obtain ⟨θ⟩ : Nonempty (S ≃* ↥JR) :=
    ⟨(e.trans CFSG.Sporadic.Fi24.fi24EquivJ).trans
      (Subgroup.subgroupOfEquivOfLe CFSG.Sporadic.Fi24.J_le_R).symm⟩
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer S) ≤ 2 :=
    Fi24PrimeAux.card_outer_le_two hcen (Fi24PrimeAux.card_mulAut_of_mulEquiv θ)
  have hO : OPrimeCoreTrivialAt 7 ↥JR :=
    OPrimeCoreTrivialAt.of_mulEquiv θ.symm (sporadicOPrimeHolds_Fi24_seven S ⟨e⟩)
  refine isLocallyBalancedAbs_two_of_autModel Nat.prime_seven (by norm_num)
    Fi24PrimeAux.fi24_autModel θ hcen hout ?_
  intro E hE hEc
  obtain ⟨d, hdE, hd1, hd⟩ :=
    exists_plane_witness_of_oPrimeCoreTrivialAt Nat.prime_seven hO hE hEc
  refine ⟨d, hdE, hd1, ?_⟩
  rw [inf_top_eq]
  have hJ : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({(d : ↥R)} : Set ↥R) ⊓ JR) = ⊥ := by
    have hmap := map_glaPPrimeCoreOf_of_injective 7 JR.subtype Subtype.val_injective
      (Subgroup.centralizer ({d} : Set ↥JR))
    have hc := map_inf_centralizer_of_injective JR.subtype Subtype.val_injective ⊤ d
    rw [hd, Subgroup.map_bot] at hmap
    rw [top_inf_eq, Subgroup.map_top, Subgroup.range_subtype] at hc
    rw [hc] at hmap
    rw [inf_comm]
    exact hmap.symm
  have hEm : Nat.card (E.map JR.subtype) = 7 ^ 2 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hEc]
  refine SporadicGtFiveRowsAux.gLAPPrimeCoreOf_R_eq_bot_of_plane hJ hEm ?_
  rintro _ ⟨x, hx, rfl⟩
  have h1 : JR.subtype (x * d) = JR.subtype (d * x) :=
    congrArg JR.subtype (IsElemAbelian.comm hE hx hdE)
  rw [map_mul, map_mul] at h1
  exact h1

end Fi24Seven

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
