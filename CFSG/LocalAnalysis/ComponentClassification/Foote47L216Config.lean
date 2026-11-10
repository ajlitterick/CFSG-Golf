module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Proof
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P2

public section

namespace CFSG.ComponentClassification.Foote47L216

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Foote47

variable {G : Type} [Group G]

@[expose] def K (a : G) : Subgroup G :=
  solomonKStarOf (Subgroup.centralizer ({a} : Set G))


@[expose] def Y (M : Subgroup G) (a : G) : Subgroup G :=
  oddResidualIn (M ⊓ Subgroup.centralizer ({a} : Set G))


end CFSG.ComponentClassification.Foote47L216
