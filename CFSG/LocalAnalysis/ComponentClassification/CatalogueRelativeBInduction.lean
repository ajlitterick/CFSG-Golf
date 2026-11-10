module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperOver
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBTwoCore
public import CFSG.LocalAnalysis.ComponentClassification.PrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup

public section

namespace CFSG.ComponentClassification.CatalogueRelativeB

open CFSG.Assembly

@[expose] def InductionHypothesis (C : GroupProp) (G : Type) [Group G] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], KProper C X →
    Nat.card X < Nat.card G → CentralTwoBInclusion.Property X

variable {C : GroupProp}

theorem proper_subgroup_B {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesis C G)
    (H : Subgroup G) (hproper : H ≠ ⊤) : CentralTwoBInclusion.Property H := by
  apply ih H (LocalAnalysis.ComponentInitial.kProper_subgroup hC hK H)
  simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hproper)

theorem smaller_quotient_B {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesis C G)
    (N : Subgroup G) [N.Normal] (hlt : Nat.card (G ⧸ N) < Nat.card G) :
    CentralTwoBInclusion.Property (G ⧸ N) :=
  ih (G ⧸ N) (CatalogueKProperOver.kProper_quotient hC hK N) hlt


end CFSG.ComponentClassification.CatalogueRelativeB
