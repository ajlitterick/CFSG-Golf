module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSubgroups

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u


@[expose] noncomputable def signalizerCommonFixed {G : Type u} [Group G]
    (subactor : Subgroup G) (signalizer : G → Subgroup G) : Subgroup G :=
  ⨅ (element : G) (_ : element ∈ subactor) (_ : element ≠ 1), signalizer element


end CFSG.RankThreeEvenClassification.Helpers
