module

public import CFSG.Quasithin.Background.RonanE42SetS

public section

namespace CFSG.Quasithin.RonanE42.Gen

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem Om_le_mQuot_bot {V : Type} [CommGroup V] {ρ : G →* MulAut V} (hρ : Function.Injective ρ)
    {n : ℕ} {A : Subgroup G} (hA : Om ρ n A) : n ≤ mQuot A ⊥ := by
  by_contra h
  push Not at h
  have hF := hA.2.2.2 ⊥ bot_le h
  apply hA.1
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  apply hρ
  rw [map_one]
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ Fx ρ ⊥ := mem_Fx.2 fun x hx => by
    rw [Subgroup.mem_bot.1 hx, map_one, MulAut.one_apply]
  rw [hF] at hv
  exact mem_Fx.1 hv a ha

theorem mQuot_bot_le_pRank {A : Subgroup G} (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    mQuot A ⊥ ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) := by
  have hAp : IsPGroup 2 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hA2 (a : G) a.2)⟩
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup G,
      E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E', -, -, hE'⟩
    exact (k.lt_two_pow_self.le).trans
      (hE'.symm.trans_le (Subgroup.card_le_card_group (H := E')))
  unfold CFSG.Open.pRank
  refine le_csSup hbdd ⟨A, le_top,
    ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hAc _ a.2 _ b.2), hA2⟩, ?_⟩
  have h := relIndex_eq_two_pow hAp ⊥
  rwa [Subgroup.relIndex_bot_left] at h

theorem aParam_le_pRank {V : Type} [CommGroup V] [Finite V] {ρ : G →* MulAut V}
    (hρ : Function.Injective ρ) : aParam ρ.range ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) := by
  apply aParam_le_of_aSet_empty
  intro A' hA'
  have hA := Om_comap_of_mem_aSet hρ hA'
  have h1 := Om_le_mQuot_bot hρ hA
  have h2 := mQuot_bot_le_pRank hA.2.1 hA.2.2.1
  omega


end CFSG.Quasithin.RonanE42.Gen
