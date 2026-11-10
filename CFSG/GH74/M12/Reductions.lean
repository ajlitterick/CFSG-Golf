module

public import CFSG.GH74.M12.Statements
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.GH74.M12

open Subgroup CFSG.Blueprint CFSG.Sporadic.Mathieu
open scoped Pointwise


instance : Finite M12Group := inferInstanceAs (Finite ↥NativeSporadic.M12)


end CFSG.GH74.M12
