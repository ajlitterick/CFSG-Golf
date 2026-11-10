module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank


@[expose] def GGTableBAut48LeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (N : Subgroup G), GGConfig 3 B Bs x L D J → GGNbr 3 B x D J y N → GGInnerDiagOn Bs N →
    ∀ labJ labN : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labN →
      GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labN (N ⧸ Subgroup.center N) →
      GGTablePRow 3 labJ labN → labJ = ⟨.A, 2, 2⟩ →
        StatedClassicalModel (↥N ⧸ Subgroup.center ↥N) .PSL 4 2 2 ∨
          48 ≤ Nat.card (ggAutomizer N Bs)


@[expose] def GGTableBAut48OmegaInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (N : Subgroup G), GGConfig 3 B Bs x L D J → GGNbr 3 B x D J y N → GGInnerDiagOn Bs N →
    ∀ labJ labN : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labN →
      GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labN (N ⧸ Subgroup.center N) →
      GGTablePRow 3 labJ labN → labJ = ⟨.A, 2, 2⟩ → labN = ⟨.twD, 4, 2⟩ →
        StatedClassicalModel (↥N ⧸ Subgroup.center ↥N) .PSL 4 2 2 ∨
          48 ≤ Nat.card (ggAutomizer N Bs)


@[expose] def GGL44CenterTrivialInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsQuasisimple Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 4 2 2 → Subgroup.center Y = ⊥

end CFSG.StandardType

end
