module

public import CFSG.CGT.Stroth77.StrothAmbient

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G] [Finite G]


abbrev IsMinimalLModuleMod {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) (C : Subgroup G) : Prop :=
  dD.IsMinimalLModule C


theorem IsMinimalLModuleMod.le_normalizer {D : Subgroup G} {τ : StrothTypeIndex}
    {dD : StrothWeakTypeData D τ} {C : Subgroup G} (h : IsMinimalLModuleMod dD C) :
    dD.L ≤ Subgroup.normalizer C :=
  h.2.1


end CFSG.CGT.Stroth77
