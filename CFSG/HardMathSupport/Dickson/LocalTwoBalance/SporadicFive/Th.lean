module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.LocalTwo

theorem sporadicTwoBalanceFive_Th :
    SporadicTwoBalanceFive .Th := by
  rintro S _ _ hsimple hnab ⟨e⟩
  obtain ⟨e'⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  let f : S ≃* Blueprint.NativeSporadic.Th := e.trans e'.symm
  have hinnTh : innerAut Blueprint.NativeSporadic.Th = ⊤ :=
    CFSG.Sporadic.ThSchreier.inner_Th
  have hinn : innerAut S = ⊤ :=
    @innerAut_eq_top_of_mulEquiv S Blueprint.NativeSporadic.Th _ _ f hinnTh
  refine isLocallyBalancedAbs_two_of_plane_witness (center_eq_bot_of_isSimpleGroup hnab) hinn ?_
  intro E hE hEc
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨d, hdE, hd1⟩ : ∃ d ∈ E, d ≠ 1 := by
    by_contra h
    push_neg at h
    have hbot : E = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      exact h
    rw [hbot, Subgroup.card_bot] at hEc
    norm_num at hEc
  have hd5 : orderOf d = 5 := orderOf_eq_prime (hE.2 d hdE) hd1
  exact ⟨d, hdE, hd1, sporadicOPrimeHolds_Th_five S ⟨f⟩ d hd5⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
