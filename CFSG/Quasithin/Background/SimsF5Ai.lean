module

import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.Permutation.SymmetricCoxeter
public import CFSG.Quasithin.Background.SimsF5Lin
public import CFSG.Quasithin.Background.SimsF5Mono
public import CFSG.Quasithin.Background.SimsF5Quat
public import CFSG.Quasithin.Background.SimsF5Stab

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix CFSG.Open
open scoped Pointwise commutatorElement


end

end CFSG.Quasithin.SimsF5
