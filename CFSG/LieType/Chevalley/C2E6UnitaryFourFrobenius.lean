module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourEquivariance
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module Matrix CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

instance : RingHomSurjective barHom := ⟨fun a => ⟨bar a, bar_bar a⟩⟩


end CFSG.LieType.Chevalley.C2E6Overlap
