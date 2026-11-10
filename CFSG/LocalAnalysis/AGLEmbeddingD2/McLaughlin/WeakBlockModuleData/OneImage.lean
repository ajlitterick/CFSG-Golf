module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.RankCount
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltTypes

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.AGLEmbeddingD2.McLaughlin

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem three_le_pRank_of_oneImage (h : AGLPair 3 M H R) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) (hH : Open.pRank 3 H = 2)
    (hM4 : 4 ≤ Open.pRank 3 M)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (ho : ClauseO M L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    3 ≤ Open.pRank 3 L := by
  obtain ⟨F, -, -, h1, h2⟩ := rank_count_one_weakSBlock h h84 h86 hD2 hH hM4 hthree hL hk1 ho hZ
  obtain ⟨y, hyP, hy3, hyC⟩ := exists_order_three_noncentral hL.le (hthree L hL) hZ
  have hy1 : y ≠ 1 := fun he => hyC (he ▸ Subgroup.one_mem _)
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hdvd : 3 ∣ Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) := by
    have := orderOf_dvd_natCard (⟨y, hyP⟩ : barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))
    rwa [Subgroup.orderOf_mk, hord] at this
  have h3 := one_le_pRank_three_of_dvd hdvd
  omega


end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
