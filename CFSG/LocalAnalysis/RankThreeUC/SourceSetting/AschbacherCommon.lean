module

public import CFSG.LocalAnalysis.RankThreeUC.Asc1930

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace SourceSetting

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G]


@[expose] def maxTwoLocalsContaining (X : Subgroup G) : Set (Subgroup G) :=
  {N | rankThreeIsMaxTwoLocal N ∧ X ≤ N}


@[expose] def oPrimeResidual (p : ℕ) (Y : Subgroup G) : Subgroup G :=
  closure {x : G | x ∈ Y ∧ ∃ k : ℕ, orderOf x = p ^ k}

@[expose] def normalClosureUnder (X H : Subgroup G) : Subgroup G :=
  ⨆ h : H, X.map (MulAut.conj (h : G)).toMonoidHom

@[expose] def QuotientIsTwoGroup (p : ℕ) (Y : Subgroup G) : Prop :=
  ∀ y ∈ Y, ∃ k : ℕ, y ^ (2 ^ k) ∈ oPrimeResidual p Y


end SourceSetting

end CFSG.LocalAnalysis.RankThreeUC
