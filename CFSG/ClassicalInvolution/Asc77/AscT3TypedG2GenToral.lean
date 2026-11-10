module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactMain
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Gen

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models

variable {p f : ℕ} [Fact p.Prime]

theorem G2CentralizersGenerate.of_nonToral (hNT : G2NonToralGenerate p) :
    G2CentralizersGenerate p :=
  fun _ hadm hp2 hq => g2CentralizersGenerate_of_nonToral hNT hp2 hq hadm


end CFSG.ClassicalInvolution.Asc77.T3Typed
