module

public import CFSG.LocalAnalysis.LargeEvenClassification.IndependentKernelCount

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse indexUniverse

theorem pGeneratorRank_eq_group_rank {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    pGeneratorRank prime Ambient = Group.rank Ambient := by
  obtain ⟨minimal, hminimalCard, hminimalGenerates⟩ := Group.rank_spec Ambient
  obtain ⟨generators, hgenerates, hcard⟩ := pGeneratorRank_generators hprime hpgroup
  apply le_antisymm
  · rw [← hminimalCard]
    exact pGeneratorRank_le_generators hprime hpgroup minimal hminimalGenerates
  · rw [← hcard]
    exact Group.rank_le hgenerates


end CFSG.LargeEvenClassification.Helpers
