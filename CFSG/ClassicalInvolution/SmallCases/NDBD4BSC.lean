module

public import CFSG.ClassicalInvolution.SmallCases.NDBD4Defs
public import CFSG.ClassicalInvolution.Asc77.AscBSE0
public import CFSG.ClassicalInvolution.Asc77.AscBSCMain

public section

namespace CFSG.ClassicalInvolution.NDB

variable {p f : ℕ} [Fact p.Prime]

theorem bootNoD4FiveComp_of (h : D4FiveCore p f) : Asc77.BSC.BootNoD4FiveComp p f := by
  intro G _ _ _ K z hS D i hi h5
  exact h G K z hS.nonabelian hS.odd hS.five hS.member hS.below hS.dconn
    (Asc77.BSC.noFuzzyFrame hS) D i hi h5

end CFSG.ClassicalInvolution.NDB
