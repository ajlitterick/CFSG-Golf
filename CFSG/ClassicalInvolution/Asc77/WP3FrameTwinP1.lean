module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameTwinCover
public import CFSG.ClassicalInvolution.Asc77.WP3FramePSCMain
public import CFSG.ClassicalInvolution.Asc77.AscIHSectE
public import CFSG.ClassicalInvolution.RouteD.TwinYP1Main
public import CFSG.ClassicalInvolution.Asc77.WP3FrameP1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.TwinY

local notation "𝒞" => CoreAssembly.conjClass

section Inputs

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinInvolution : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z

variable {p f}

theorem NoThreeFund.of_small {tY : StatedLieTag} {nY : ℕ} (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible tY nY p f)
    (hsmall : (tY = .PSp ∧ nY = 2) ∨ (tY = .PSL ∧ nY = 4) ∨ (tY = .PSU ∧ nY = 4) ∨
      (tY = .POmegaOdd ∧ nY = 3) ∨ (tY = .POmegaMinus ∧ nY = 4)) :
    NoThreeFund p f tY nY :=
  fun A hA B hB C hC => smallNoThree tY nY f hadm hp hq hsmall A hA B hB C hC

end Inputs

end CFSG.ClassicalInvolution.Asc77
