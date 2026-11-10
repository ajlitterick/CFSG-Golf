module

public import CFSG.Quasithin.H13.A5S1517
public import CFSG.Quasithin.H13.A5S135

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint

@[expose] def Input13515 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V)
    (H : Subgroup G), H ∈ S.Hz → H ≤ Subgroup.normalizer (S.L1 : Set G) →
    ¬ IsElemAbelian 2 (conjClosure S.V3 H) → ∃ I : Subgroup G, Data13515 S H I

@[expose] def Input13518 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1) →
    ∃ H ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H) ∧
      H ≤ Subgroup.normalizer (S.L1 : Set G)

@[expose] def Input136 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    ¬ IsElemAbelian 2 (conjClosure V S.G1)

namespace Setting


end Setting

end CFSG.Quasithin.H13.A5
