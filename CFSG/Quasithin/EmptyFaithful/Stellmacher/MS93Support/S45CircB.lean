module

public import CFSG.Quasithin.MS93.S45IV

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def S45C1aQ4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Ctx M T L φ), 4 ≤ Fintype.card F →
    ∀ δ : Vtx (puAmalgam c.hyp.le), IsMVtx _ δ →
      Vcirc c.hyp.le L δ ⊓ ZM _ δ ≤ Uloc c.hyp.le L δ ⊔ Hloc c.hyp.le L δ

@[expose] def S45C1bQ4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Ctx M T L φ), c.HZV → 4 ≤ Fintype.card F →
    ∀ (p : ℕ → Vtx (puAmalgam c.hyp.le)) (N : ℕ), IsGoodPath _ p N →
    ∀ a : ℕ, Even a → 34 ≤ a → a + 30 ≤ N →
    ¬ Zloc c.hyp.le L (p a) ≤ Hloc c.hyp.le L (p a) →
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ ZM _ (p a) ≤ Vcirc c.hyp.le L (p a)

section Card


end Card

end CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support
