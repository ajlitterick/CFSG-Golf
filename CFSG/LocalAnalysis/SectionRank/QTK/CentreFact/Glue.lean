module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Defs
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.SectionRank.QTK.A134Pi
public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.LocalAnalysis.SectionRank.QTK.Section

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup
open CFSG.Assembly.RankThreeEven (localRank)

theorem OddBound.of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T] {r : ℕ}
    (hr : 1 < r) (e : S ≃* T) (h : OddBound r T) : OddBound r S :=
  fun R hR hR2 => pRank_normalizer_le_of_mulEquiv e hr h R hR hR2


end CFSG.SectionRank.QTK.CentreFact
