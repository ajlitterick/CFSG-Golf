module

public import CFSG.YGroups.Defs

public section

namespace CFSG.YGroups

@[expose] def Ctil : Subgroup (YGroup 2 3 3) :=
  Subgroup.closure (yGen 2 3 3 '' {c | c < 9 ∧ c ≠ 2})


end CFSG.YGroups

end
