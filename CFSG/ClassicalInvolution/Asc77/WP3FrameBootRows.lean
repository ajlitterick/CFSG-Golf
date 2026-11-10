module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootChain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameTwinP1
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Balance.BootRank3 (omegaConnected_of_routeD)
open CFSG.ClassicalInvolution.RouteD.TwinY

local notation "𝒞" => CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

section TwinRows

variable {p f : ℕ} [Fact p.Prime]

@[expose] def AEmptyTwinRow (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : LTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M

end TwinRows

end CFSG.ClassicalInvolution.Asc77
