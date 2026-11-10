module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelSignMain
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelPerp

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

theorem e7SignPerp {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    RouteD.SignPerp (RouteD.TypeE8.F7 p f) (GaloisField p f) :=
  (RouteD.TypeE8.signPerp_iff p f).2 ⟨e7Sign hp2 hq, e7Perp2 hp2 hq⟩

end CFSG.ClassicalInvolution.ModelFacts.E7Model
