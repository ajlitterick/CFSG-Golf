module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrRankGap

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type*} [Group G]

@[expose] noncomputable def gsMeasure (c : G) (K : Subgroup G) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex ((pPrimeCore 2 K).index,
    toLex (pRank 2 ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G) ⊓ coreActionKernel K),
      2 ^ (Nat.card ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G))).factorization 2))


end CFSG.ComponentClassification.UnbalancedCorr
