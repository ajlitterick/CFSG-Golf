module

public import CFSG.Quasithin.H13.A5S136d
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Quasithin.E3
open CFSG.Blueprint

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

structure Concl136 : Prop where
  hab : IsElemAbelian 2 (conjClosure V S.G1)
  h24 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
    (∃ u : ↥V, u ≠ 1 ∧ IsSing (S.frame.ψ u) ∧
      V ⊓ conjSub g⁻¹ V = Subgroup.zpowers (u : G)) ∧ ⁅V, conjSub g⁻¹ V⁆ = ⊥
  hr : rParam V = 3
  hw : 1 < wParam T V
  hn : ∀ H : Subgroup G, InH T H → ¬ H ≤ Subgroup.normalizer (L : Set G) → 1 < E1.nParam H
  hsolv : ∀ H : Subgroup G, InH T H → Group.IsSolvable ↥H →
    H ≤ Subgroup.normalizer (L : Set G)
  h2661 : ∀ H ∈ S.Hz, ∀ K ∈ cComp H, ¬ K ≤ Subgroup.normalizer (L : Set G)


end Setting


end CFSG.Quasithin.H13.A5
