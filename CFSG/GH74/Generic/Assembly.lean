module

public import CFSG.GH74.RouteRefine
public import CFSG.GH74.Generic.ComponentShapes

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.Blueprint

@[expose] def S_shapeCase
    (P : ∀ {G : Type} [Group G] (x : G), Subgroup (CentralizerBar x) → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
      (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
      (∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥) →
      ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K → GLS.InG2 ↥K →
        P x K → Catalog G


end CFSG.GH74.Generic
