module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec6S
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Core
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec5S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def HasPSL6Sylow (B : Type) [Group B] : Prop :=
  ∃ (p f : ℕ) (S : Type) (_ : Group S), p.Prime ∧ 0 < f ∧ p ^ f % 4 = 3 ∧
    CFSG.Blueprint.LieModel S .PSL 6 p f ∧
    ∃ (P : Sylow 2 B) (P' : Sylow 2 S), Nonempty (↥P ≃* ↥P')


@[expose] def FooteSylowL6 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → HasPSL6Sylow S →
    (∃ p f : ℕ, p.Prime ∧ 0 < f ∧ p ^ f % 4 = 3 ∧ CFSG.Blueprint.LieModel S .PSL 6 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 0 < f ∧ p ^ f % 4 = 1 ∧ CFSG.Blueprint.LieModel S .PSU 6 p f)

@[expose] def SettingExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ t : G, t ∈ centralizer (L : Set G) → orderOf t = 2 → ∃ s : Setting3 G L, s.t = t

@[expose] def Y6F : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.toCtx5.Facts5 → c.Facts6 → c.Four →
      ∃ (z : G) (K : Subgroup G), Case3Core G z K

end CFSG.OddStandard.HigherRank.YamadaG23
