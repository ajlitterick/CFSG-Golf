module

public import CFSG.Quasithin.Background.SimsF5Inv

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix

local notation:max "mat(" g ")" => ((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3))


end

end CFSG.Quasithin.SimsF5
