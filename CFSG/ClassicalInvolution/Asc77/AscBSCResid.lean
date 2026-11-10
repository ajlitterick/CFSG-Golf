module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootMain
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]


structure BootSetting {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  member : IsClassicalMember p f K z
  below : CITBelowU p f (Nat.card G)
  dconn : DConnected (𝒞 K)
  data : BootData p f (𝒞 K)
  noTriple : ¬ IndepTriple p f (𝒞 K)

@[expose] def BootNoAllA1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z,
      ¬ ∀ i, D.tag i = .PSL ∧ D.rank i = 2


@[expose] def BootNoM3Twin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
      (D.tag i = .PSL ∨ D.tag i = .PSU) → D.rank i = 3 → D.card ≤ 2


@[expose] def BootNoManyTwins : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
      Asc77.ListedTwin (D.tag i) (D.rank i) → D.card ≤ 3


end CFSG.ClassicalInvolution.Asc77.BSC
