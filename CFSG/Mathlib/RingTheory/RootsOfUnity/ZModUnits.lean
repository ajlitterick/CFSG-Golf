module

public import TauCeti.RingTheory.RootsOfUnity.ZMod

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

variable {L : Type*} [Field L]

@[expose] def rootsOfUnityAddHom (p : ℕ) :
    Additive (rootsOfUnity p L) →+ Additive Lˣ where
  toFun x := Additive.ofMul (x.toMul : Lˣ)
  map_zero' := rfl
  map_add' _ _ := rfl


@[expose] def zmodToUnits (p : ℕ) [NeZero p] (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) :
    ZMod p →+ Additive Lˣ :=
  (rootsOfUnityAddHom (L := L) p).comp hζ.zmodEquivRootsOfUnity.toAddMonoidHom


end CFSG.LieType.AlgebraicGroups
