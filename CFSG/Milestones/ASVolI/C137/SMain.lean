module

public import CFSG.Milestones.ASVolI.C137.SJ
public import CFSG.Milestones.ASVolI.C137.A6Ent
public import CFSG.Milestones.ASVolI.C135.WMain
public import CFSG.Milestones.ASVolI.C137.Cases
public import CFSG.Milestones.ASVolI.C137.Setup
public import CFSG.Quasithin.H13.GoldschmidtC137L32Blk
public import CFSG.Quasithin.H13.GoldschmidtC137L32Lie
public import CFSG.Quasithin.H13.GoldschmidtC137SQFinal
public import CFSG.Quasithin.H13.GoldschmidtC137Tail

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.ASVolI.ChC
open CFSG.Quasithin.L3 CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137

variable {G : Type} [Group G]


theorem burnsideC137_rkIdx_of_card {W : Type} [CommGroup W] [Finite W] (H : Subgroup W) {a : ℕ}
    (hW : Nat.card W = 2 ^ 6) (hH : Nat.card H = 2 ^ a) : rkIdx H = 6 - a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := rk_add_rkIdx H
  unfold rk at h
  rw [hW, hH, padicValNat.prime_pow, padicValNat.prime_pow] at h
  omega

namespace burnsideC137_SCtx

variable [Finite G] {X T L P U U₁ U₂ : Subgroup G} {α : ↥L →* Γ}
  {β₁ : ↥U₁ →* Multiplicative Vec} {β₂ : ↥U₂ →* Multiplicative Vec}
  (h : burnsideC137_SCtx X T L P U α U₁ U₂ β₁ β₂)
include h


theorem hC (hRL : autI h.hU (pCoreOf 2 P) ≤ autI h.hU L) :
    ∀ B, ¬ IsStrongFFStarOffender (autI h.hU (pCoreOf 2 P)) B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro B ⟨hoff, hlt⟩
  have hBL : B ≤ autI h.hU L := hoff.1.trans hRL
  have hsq : ∀ b ∈ B, b * b = 1 := fun b hb => by
    rw [← pow_two]
    exact hoff.2.2.1.2 b hb
  have hc : Nat.card (IntMod U h.hU) ≤ Nat.card B * Nat.card (fixV B) := by
    have := hoff.2.2.2 ⊥ bot_le
    rw [Subgroup.card_bot, one_mul, B5.fixV_bot_eq_top, Subgroup.card_top] at this
    exact this
  obtain ⟨-, -, -, h4, h16⟩ := burnsideC137_offender h.hs h.hU hBL hoff.2.1 hsq hc
  have hrk : rk B = 2 := by
    unfold rk
    rw [h4, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have hrkI : rkIdx (fixV B) = 2 :=
    burnsideC137_rkIdx_of_card _ (by rw [burnsideC137_card_U h.hs h.hU]; norm_num)
      (a := 4) (by rw [h16]; norm_num)
  unfold rAV at hlt
  rw [hrk, hrkI] at hlt
  norm_num at hlt


end burnsideC137_SCtx

section Canonical


end Canonical

end CFSG.ASVolI
