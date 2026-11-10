module

public import CFSG.ThirdParty.TauCeti.DynamicSmooth

public noncomputable section

open WithConv TauCeti

namespace CFSG.LieType.AlgebraicGroups.DynamicUnipotent

universe u v w


variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

local notation "Pideal" l => (CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal l)
local notation "Uideal" l => (CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal l)


end CFSG.LieType.AlgebraicGroups.DynamicUnipotent
