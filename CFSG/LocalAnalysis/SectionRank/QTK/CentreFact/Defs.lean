module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup

@[expose] def OddBound (r : ℕ) (S : Type) [Group S] [Finite S] : Prop :=
  ∀ R : Subgroup S, R ≠ ⊥ → IsPGroup 2 R → CFSG.Open.pRank r (normalizer (R : Set S)) ≤ 2


end CFSG.SectionRank.QTK.CentreFact
