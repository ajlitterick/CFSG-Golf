module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime CFSG.RankThreeCoreUniqueness.Helpers
   Subgroup


@[expose] def KFactCaseTwoFieldInvertThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsCaseTwoGroup 3 K → ∀ φ : MulAut K, φ ^ 3 = 1 →
    (¬ ∃ y : K, φ = MulAut.conj y) → ∀ t : K, orderOf t = 3 → φ t = t →
      ∃ s : K, s ^ 2 = 1 ∧ φ s = s ∧ s * t * s⁻¹ = t⁻¹

end CFSG.LocalAnalysis.RankThreeTheoremC
