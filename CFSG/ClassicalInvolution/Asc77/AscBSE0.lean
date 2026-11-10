module

public import CFSG.ClassicalInvolution.Asc77.AscBSDResid

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]


@[expose] def BootNoD4FiveComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
      (D.tag i = .POmegaPlus ∧ D.rank i = 4) → D.card = 5 → False


end CFSG.ClassicalInvolution.Asc77.BSC
