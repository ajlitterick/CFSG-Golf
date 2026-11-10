module

public import CFSG.GH74.Milestone
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.GH74

open Blueprint

@[expose] def S_restrictedEvenThin : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
      (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
      (∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥) → GLS.IsRestrictedEvenType G →
        Assembly.evenRank G ≤ 2


@[expose] def S_generic' : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
      (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
      (∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥) → GLS.L2Meets G GLS.InG2 → Catalog G

theorem generic_of_catalog
    (h : S_generic') : S_generic :=
  fun G _ _ hs hnonab hrank hgen hK hnab hLx hg =>
    s_filter G (h G hs hnonab hrank hgen hK hnab hLx hg) hnonab hrank hgen


end CFSG.GH74
