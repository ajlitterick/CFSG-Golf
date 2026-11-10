module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteDefs
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I161a2
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
public import CFSG.CGT.PushingUpLit.CGT6.SixFour
public import CFSG.CGT.PushingUpLit.CGT6.SixSixteen
public import CFSG.CGT.PushingUpLit.Glue.ClassXBasic
public import CFSG.CGT.PushingUpLit.Glue.RadicalSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.GH74.GLS.IVK.Proofs2.OddTools
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Multiplier

theorem center_eq_bot_of_fsEndMarking
    {G : Type} [Group G] [Finite G] {K : Subgroup G} {P : LargeEvenLabel → Prop}
    (hP : ∀ lab, P lab → ((lab.tag = .D ∧ lab.rank = 6) ∨ (lab.tag = .twD ∧ lab.rank = 7) ∨
      (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1)
    (h : LargeEvenMarking ↥K (fun lab _ _ _ _ _ => P lab)) : Subgroup.center K = ⊥ := by
  have hq : CFSG.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp
      (isQuasisimple_of_largeEvenMarking h)
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_markedModel h
  obtain ⟨R, _, I, F, -, -, θ, hPl, hm⟩ := largeEvenRawDatum_exists hraw
  have hmod := CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hm
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement R _ _ _ _ hmod
  have hlab := hP lab hPl
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier R) = 1 := by
    rw [Nat.card_congr e.toEquiv]
    obtain ⟨t, r, n⟩ := lab
    obtain ⟨ht, hn⟩ := hlab
    dsimp only at ht hn
    subst hn
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [markTag, markRank, markChar, markDeg, genericOrders, exceptionalOrders,
        Nat.card_congr Multiplicative.toAdd]
  haveI : Finite (CFSG.Open.griessHopfMultiplier R) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact one_ne_zero)
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq θ
  rw [hcard, Nat.dvd_one] at hd
  exact Subgroup.eq_bot_of_card_eq _ hd


end CFSG.StandardType.FrameRoute

end
