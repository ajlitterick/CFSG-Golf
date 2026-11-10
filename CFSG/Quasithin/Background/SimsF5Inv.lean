module

public import CFSG.Quasithin.Background.SimsF5Ai
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Extension
public import CFSG.Quasithin.Background.SimsF5Main

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix

local notation:max "mat(" g ")" => ((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3))

local instance inv_two : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)


end

end CFSG.Quasithin.SimsF5
