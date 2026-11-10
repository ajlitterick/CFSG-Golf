module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcComp
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.AGLEmbeddingD2

@[expose] def GGSeitzExcTitsThreeInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), d.1 = .tits →
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ X : Subgroup K, X ≠ ⊤ → ¬ 3 ∣ X.index →
        Group.IsSolvable ↥X ∨
          (IsSimpleGroup ↥(commutator ↥X) ∧ Nat.card ↥(commutator ↥X) = 5616)

@[expose] def GGSeitzExcTitsFiveInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), d.1 = .tits →
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ X : Subgroup K, X ≠ ⊤ → ¬ 5 ∣ X.index →
        Group.IsSolvable ↥X ∨
          (IsSimpleGroup ↥(commutator ↥X) ∧ Nat.card ↥(commutator ↥X) = 7800)

theorem ggCenter_eq_bot_of_not_isSolvable {S : Type} [Group S] [IsSimpleGroup S]
    (h : ¬ Group.IsSolvable S) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hc | hc
  · exact hc
  · refine absurd (Group.isSolvable_of_comm fun a b => ?_) h
    have hb : b ∈ Subgroup.center S := hc ▸ Subgroup.mem_top b
    exact (Subgroup.mem_center_iff.mp hb a)

theorem ggExists_component_of_layer_ne_bot {G : Type} [Group G] {A : Subgroup G}
    (hL : LargeEvenLayer A ≠ ⊥) : ∃ C : Subgroup G, IsComponentOf C A := by
  by_contra hcon
  push Not at hcon
  exact hL (sSup_eq_bot.mpr fun C hC => absurd hC (hcon C))

section Marked


end Marked

end CFSG.StandardType
