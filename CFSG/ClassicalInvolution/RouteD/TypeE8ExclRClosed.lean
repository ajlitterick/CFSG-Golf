module

public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclRFinal
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclLayerPsi

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

variable {p f : ℕ} [Fact p.Prime]

theorem e8ClassExcluded_of_three (hConn : p ≠ 2 → 5 ≤ p ^ f → Fund12Connected p f)
    (hRow : E8D8Row' p f) (hD8 : E8D8NoThreeAdj p f) : E8ClassExcluded p f := by
  intro G _ _ _ hnab K z S hshape c β hβ t htβ hKβ ht g p₀ hT
  exact e8ClassExcluded (ModelFacts.E7Model.e7LayerEquiv S.odd S.five) (hConn S.odd S.five)
    hRow hD8 G hnab K z S hshape c β hβ t htβ hKβ ht g p₀ hT

end CFSG.ClassicalInvolution.RouteD.TypeE8
