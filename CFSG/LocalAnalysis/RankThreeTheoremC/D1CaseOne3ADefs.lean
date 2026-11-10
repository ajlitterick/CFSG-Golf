module

public import CFSG.LocalAnalysis.AGLEmbedding.D1CompCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G]

structure D1OneSmall3Data (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  cfg : D1ComponentConfig3 p P M H R Rbar
  comp : IsComponentOf K ⊤
  center : Subgroup.center K = ⊥
  noncyclic : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
    Subgroup (H ⧸ primeComplementCore (G := H) p))
  z : ∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
    z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  small : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmall3Data.toCore (hd : D1OneSmall3Data p P M H R Rbar K) :
    D1CompCore p P M H R Rbar K :=
  ⟨hd.cfg.ext.toD1Escape, hd.cfg.rbar, hd.cfg.red, hd.comp, hd.center, hd.noncyclic, hd.z⟩


end Data

end CFSG.LocalAnalysis.RankThreeTheoremC
