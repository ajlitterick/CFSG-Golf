module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure315Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.GorensteinWalter
open scoped Pointwise


@[expose] def burnsideA315y_FittingStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (B S : Subgroup X), IsMulCommutative ↥B → Odd (Nat.card ↥B) →
    IsPGroup 2 ↥S → (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X) →
    (∃ R : Subgroup X, R ≤ S ∧ R ≠ ⊥ ∧ B ≤ Subgroup.normalizer (R : Set X) ∧
      S ≤ Subgroup.normalizer (R : Set X)) ∨ S ≤ Subgroup.normalizer (B : Set X)


end CFSG.ASVolI
