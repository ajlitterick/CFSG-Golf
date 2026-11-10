module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoFacts46
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y} {k : ℕ}

theorem burnsideF46_hval (T : TitsHyp c k) : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  CFSG.ASVolI.ChF.burnsideF4a_hval T.faithful T.thick1 T.thick2


end CFSG.ASVolI
