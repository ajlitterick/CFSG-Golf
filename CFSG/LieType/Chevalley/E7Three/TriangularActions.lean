module

public import CFSG.LieType.Chevalley.E7Three.CoordinateActions

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.TriangularActions

open CFSG.LieType.Chevalley.E7Three.CoordinateActions

abbrev P := ZMod 3 × ZMod 3 × ZMod 3

@[expose] def x : MulAut D := u ^ 2
@[expose] def z : MulAut D := v * u * v⁻¹
@[expose] def y : MulAut D := w * z * w⁻¹


end CFSG.LieType.Chevalley.E7Three.TriangularActions
