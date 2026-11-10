module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.X3324
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement Pointwise

namespace C4Fix3323

variable {G : Type} [Group G]

theorem card_Q_of_case1 {T R L : Subgroup G}
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    (h1 : IsC134Case1 (L ⊔ T) R L) : Nat.card ↥(c134Q (L ⊔ T) L) = 8 := by
  obtain ⟨-, nF, F, _, _, hFc, -, α', hα's, hα'k, β, hβs, hβk, -⟩ := h1
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ ⟨hα's, hα'k⟩)
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩), Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_eq_fintype_card, hF]
  simp


end C4Fix3323

end CFSG.Quasithin.H13
