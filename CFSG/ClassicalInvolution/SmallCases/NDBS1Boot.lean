module

public import CFSG.ClassicalInvolution.SmallCases.NDBS1Plus
public import CFSG.ClassicalInvolution.Asc77.AscBSCMain

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

end CFSG.ClassicalInvolution.NDB
