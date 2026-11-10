module

public import CFSG.ClassicalInvolution.SmallCases.DSplitBridge
public import CFSG.ClassicalInvolution.Generic.TypeCSetup2Assembly
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ClassicalInvolution.SmallConn

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.ConnectedA2 CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

@[expose] def NoDataBootD (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      DConnected (𝒞 K) → ¬ BootData p f (𝒞 K) →
      ExactMembers (𝒞 K) ∧ LocalOddCentral (𝒞 K) {z}


section A2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]


end A2

theorem noDataD_of_noDataBootD (h : NoDataBootD p f) : NoDataD p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hD hB
  obtain ⟨hex, hp1⟩ := h G hnab hp2 hq K z hz hBelow h3 h4 hD hB
  exact (deltaConnected_iff K).mpr
    (routeD_deltaConnected_of_dConnected_of_exact hnab hp2 hq hz hBelow hD hex hp1)


end CFSG.ClassicalInvolution.SmallConn
