module

public import CFSG.ClassicalInvolution.SmallCases.NDBC8
public import CFSG.ClassicalInvolution.SmallCases.NDBF

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

end CFSG.ClassicalInvolution.NDB
