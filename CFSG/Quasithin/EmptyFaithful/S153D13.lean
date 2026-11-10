module

public import CFSG.Quasithin.EmptyFaithful.S153D22

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Stage15313 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 2 →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I → ¬ CharTwo I

@[expose] def Facts15311All : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 2 →
      ∀ H : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M H → Facts15311 T M V₁ Yp H


end CFSG.Quasithin
