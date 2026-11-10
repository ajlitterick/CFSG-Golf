module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Reduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Strong
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3CyclicInt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {G : Type} [Group G] [Finite G]

@[expose] def D2L34BetaMSolvableStrong3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → Group.IsSolvable M → GLBStronglyEmbedded 3 M

@[expose] def D2L34BetaMSolvableCyclic3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → Group.IsSolvable M → ∀ g : G, g ∉ M →
      3 ∣ Nat.card ↥(M ⊓ GLBConj g M) → CFSG.Open.pRank 3 (M ⊓ GLBConj g M) ≠ 1

theorem D2L34BetaMSolvableCyclic3.toStrong3 (h : D2L34BetaMSolvableCyclic3 G) :
    D2L34BetaMSolvableStrong3 G := by
  intro d P M A H R Rbar K ctx hs
  by_contra hns
  obtain ⟨g, hg, hdvd, hrk⟩ := ctx.exists_cyclic_of_not_stronglyEmbedded hns
  exact h d P M A H R Rbar K ctx hs g hg hdvd hrk


theorem D2L34BetaMSolvableCenter3.toStrong3 (h : D2L34BetaMSolvableCenter3 G) :
    D2L34BetaMSolvableStrong3 G :=
  fun _ _ _ _ _ _ _ _ ctx hs => d2L34BetaMSide3_stronglyEmbedded_of_center h ctx hs

theorem d2L34BetaMSide3_of_inputs_strong
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59)
    (hSS : D2L34BetaMSolvableStrong3 G) (hr2 : FFRankTwoInput3 G) (hnc : FFNoncyclicInput3 G)
    (hnonc : D2L34BetaMSideNonConstrainedInput3 G) : D2L34BetaMSide3 G := by
  intro hS hD1 M hM ha hb P A H R hp hMP d Rbar K hc hAll
  have h : D2L34SideCtx3 G d P M A H R Rbar K := ⟨hS, hD1, hM, ha, hb, hp, hMP, hc, hAll⟩
  refine ⟨fun hs => hSS d P M A H R Rbar K h hs, fun hstr => ?_⟩
  have := h.amb
  have hKmax : D2L34Kmax H := D2L34BetaConf3.d2L34Kmax hc hstr hAll.onlyL34At
  obtain ⟨U, hU, hUsyl, hAU, hNHU, hsylU⟩ :=
    D2L34BetaConf3.exists_base_of_cover hFF hc hstr hAll.onlyL34At
  refine exists_s3Parabolic_of_permuted3 ?_
  by_cases hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M
  · obtain ⟨P₀, hP₀M, hP₀, hNn⟩ :=
      exists_normal_order_three_of_ctx3 hFF hI59 hr2 hnc h hstr hcon
    exact d2L34BetaMSidePermuted3_of_orderThree hc hstr hP₀M hP₀ hNn hU hNHU hsylU
  · obtain ⟨P₁, L, hLM, hLn, hP₁L, hP₁c, hperm', hAL, hsimple⟩ :=
      hnonc d P M A H R Rbar K h hstr hKmax hcon U hU hUsyl hAU hNHU hsylU
    exact d2L34BetaMSidePermuted3_of_nonconstrained hc hstr hU hNHU hLM hLn hP₁L hP₁c hperm'
      hAL hsimple


end CFSG.LocalAnalysis.RankThreeTheoremC
