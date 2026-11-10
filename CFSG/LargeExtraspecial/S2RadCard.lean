module

public import CFSG.LargeExtraspecial.S2SixAut
public import CFSG.LargeExtraspecial.S2SixSp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem natCard_submodule (W : Submodule (ZMod 2) V) :
    Nat.card W = 2 ^ finrank (ZMod 2) W := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]


end S2

end CFSG.LargeExtraspecial
