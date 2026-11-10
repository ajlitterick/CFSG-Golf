module

public import CFSG.Milestones.ASVolI.F45.TitsLoc
public import CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoBridge

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section Range

variable {G H : Type*} [Group G] [Group H] {f : G →* H}


end Range

variable {α : RankTwoAmalgam.{0}} {Y Yb : Type} [Group Y] [Group Yb]

section Lift


end Lift

section Transfer

variable {β : α.Completion Y} {ι : α.Completion Yb} (hβ : β.IsFaithful) (hι : ι.IsFaithful)

include hβ hι


end Transfer

section Nbrs


variable {β : α.Completion Y} {ι : α.Completion Yb} (hβ : β.IsFaithful) (hι : ι.IsFaithful)

include hβ hι


end Nbrs

section Orbits

@[expose] def burnsideF46_TwoOrb (c : α.Completion Y) (u : c.Γ) (n : ℕ) : Prop :=
  ∃ q₁ ∈ GPath.nbPaths c.graph u n, ∃ q₂ ∈ GPath.nbPaths c.graph u n,
    GPath.nbPaths c.graph u n = pathOrbit (stv c u) q₁ ∪ pathOrbit (stv c u) q₂ ∧
    Disjoint (pathOrbit (stv c u) q₁) (pathOrbit (stv c u) q₂) ∧
    Nat.card ↥(pathOrbit (stv c u) q₁) = Nat.card ↥(pathOrbit (stv c u) q₂)


end Orbits

section Smul


end Smul

end CFSG.ASVolI
