module

public import CFSG.ClassicalInvolution.Q3.Q3ZCheck
public import CFSG.ClassicalInvolution.Q3.Q3ZGen
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.CosetTable CFSG.Assembly.LowTwoRank


@[expose] def V6Collapse : Prop :=
  ∀ k : Fin 24, gluingComplete k = false → ∀ {G : Type} [Group G] (g : Fin 12 → G),
    RelsHold g (v6aWords k) → ∀ i, g i = 1


end CFSG.ClassicalInvolution.Q3.Q3Z
