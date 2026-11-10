module

public import CFSG.Quasithin.Background.SimsF5Ai
public import CFSG.Quasithin.Background.SimsF5Par
public import CFSG.Quasithin.Background.SimsF5Main

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix CFSG.Open CFSG.Quasithin.SimsF5Lat
open scoped Pointwise

local notation:max "mat(" g ")" => ((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3))


end
