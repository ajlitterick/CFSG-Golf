module

public import CFSG.ClassicalInvolution.Asc77.WP3S28BIndep
public import CFSG.ClassicalInvolution.SmallCases.NDBStmt
public import CFSG.ClassicalInvolution.Asc77.WP3SCRBoot
public import CFSG.ClassicalInvolution.Asc77.AscFusionS14
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalAll
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwAll
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected

section NDB

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

variable {Ω : Set (Subgroup G)}

theorem bootData_of_indepTriple (h : CoreAssembly.IndepTriple p f Ω) : BootData p f Ω := by
  obtain ⟨K, z, hK, hcomm, hel, hcard⟩ := h
  refine ⟨K 0, z 0, Subgroup.closure (Set.range z), (hK 0).1, (hK 0).2, hel, hcard,
    Subgroup.subset_closure ⟨0, rfl⟩, ?_⟩
  exact triple_centralizes hK hcomm 0

end NDB

end CFSG.ClassicalInvolution.Asc77.S28B
