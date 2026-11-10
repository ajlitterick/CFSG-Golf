module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.PairwiseFixedGrowth
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedSylowConjugacy

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem SignalizerPrimeCompatible.inf {G : Type u} [Group G] [Finite G]
    (prime subgroupPrime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (first second : Subgroup G)
    (hfirst : SignalizerPrimeCompatible prime subgroupPrime actor signalizer first)
    (hsecond : SignalizerPrimeCompatible prime subgroupPrime actor signalizer second) :
    SignalizerPrimeCompatible prime subgroupPrime actor signalizer (first ⊓ second) :=
  SignalizerPrimeCompatible.of_le prime subgroupPrime actor signalizer first _ hfirst inf_le_left
    (normalizes_inf_of_normalizes_both actor first second hfirst.1.normalized hsecond.1.normalized)


end CFSG.RankThreeEvenClassification.Helpers
