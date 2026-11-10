module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Reduction
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Subnormal

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement


@[expose] def Q8TwinRecogEx (Ex : ∀ (Y : Type) [Group Y] [Finite Y], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup ↥(genFittingFStar Y) →
    (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) → CIT3Below (Nat.card Y) →
    TightBelow (Nat.card Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) → TightHasLift R t ∨ Ex Y


end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
