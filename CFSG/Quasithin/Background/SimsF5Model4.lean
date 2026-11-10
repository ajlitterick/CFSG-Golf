module

public import CFSG.Quasithin.Background.SimsF5Ai
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Quasithin.Background.SimsF5Main

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix CFSG.Open CFSG.ASVolI.ChF
open scoped Pointwise commutatorElement

local notation "M6" => Matrix (Fin 6) (Fin 6) (ZMod 3)


namespace M4Data


end M4Data


end

end CFSG.Quasithin.SimsF5
