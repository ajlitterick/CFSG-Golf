module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalClassical

public section

namespace CFSG.ComponentClassification.StandardRecognition

open CFSG.Assembly


@[expose] def M12J2DoubleCoverExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → ∀ L : Subgroup G, Assembly.ComponentType.IsStandardSubgroup L →
    (∀ x : G, orderOf x = 2 → Assembly.oddCore (Subgroup.centralizer ({x} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)),
      IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))) →
      Nat.card (Subgroup.center L) = 2 →
      ¬ (Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .M12 ∨
        Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .J2)

@[expose] def M12J2CentralTwoGroupOrderBound : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Assembly.IsQuasisimple L →
    IsPGroup 2 (Subgroup.center L) →
    (Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .M12 ∨
      Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .J2) →
    Nat.card (Subgroup.center L) ≤ 2


@[expose] def StandardRecognitionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → ∀ L : Subgroup G, Assembly.ComponentType.IsStandardSubgroup L →
      InCatalog G

end CFSG.ComponentClassification.StandardRecognition
