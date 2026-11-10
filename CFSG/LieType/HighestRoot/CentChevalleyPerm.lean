module

public import CFSG.LieType.HighestRoot.CentChevalley

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

noncomputable abbrev pairGroup
    (τ : Tag) (K : Type) [Field K] (β : Fin τ.rank → ℤ) :
    Subgroup (ModGL τ K) :=
  rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)


end CFSG.LieType.HighestRoot
