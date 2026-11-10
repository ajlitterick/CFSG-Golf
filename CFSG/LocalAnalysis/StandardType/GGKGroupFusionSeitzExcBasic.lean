module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitz
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltDefining

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.AGLEmbeddingD2

@[expose] def GGKFSeitzLTwoEight (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d ∧ q.p = 2 ∧
    q.exponent = 3 ∧ d.1 = .A 1 q

@[expose] def GGKFSeitzLThreeFour (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d ∧ q.p = 2 ∧
    q.exponent = 2 ∧ d.1 = .A 2 q

@[expose] def GGKFSeitzUFourTwo (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d ∧ q.p = 2 ∧
    q.exponent = 1 ∧ d.1 = .twistedA 3 q

@[expose] def GGKFSeitzSpSixTwo (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d ∧ q.p = 2 ∧
    q.exponent = 1 ∧ d.1 = .B 3 q

@[expose] def GGKFSeitzSpEightTwo (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d ∧ q.p = 2 ∧
    q.exponent = 1 ∧ d.1 = .B 4 q

@[expose] def GGKFSeitzTitsThree (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .tits

@[expose] def GGKFSeitzTitsFive (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .tits

@[expose] def GGKFSeitzSzThirtyTwo (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .suzuki 2


section Common

variable {W : Type} [Group W] {p : ℕ} {H E : Subgroup W}

theorem ggSeitzExc_subgroupOf_ne_top (hKH : ¬ CFSG.generalizedFitting W ≤ H) :
    H.subgroupOf (CFSG.generalizedFitting W) ≠ ⊤ := fun h =>
  hKH (Subgroup.subgroupOf_eq_top.mp h)

theorem ggNot_isSolvable_of_layer_ne_bot (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥) :
    ¬ Group.IsSolvable ↥H := by
  intro hH
  apply hL
  refine sSup_eq_bot.mpr fun C hC => ?_
  exfalso
  have : Group.IsSolvable (GGHypQuot H) := inferInstance
  exact ggComponent_not_le_of_isSolvable hC (A := ⊤) inferInstance le_top


end Common

end CFSG.StandardType
