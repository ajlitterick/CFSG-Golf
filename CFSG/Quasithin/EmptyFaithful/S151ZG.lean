module

public import CFSG.Quasithin.EmptyFaithful.S151ZD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def RankTwoSimpleNotA38 : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G), (IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) →
    ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)


@[expose] def Input15122ThreeCZL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120ThreeC T Mc Z₁ L → ZL2 (s1516 T Z₁) L


end CFSG.Quasithin
