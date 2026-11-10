module

public import CFSG.Milestones.ASVolI.B4Ext.Defs
public import CFSG.Quasithin.Background.SmithB49N4
public import CFSG.Quasithin.Background.SmithB49D5

public section

namespace CFSG.ASVolI

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B5.Ln CFSG.Quasithin.B5.B49 Matrix Module
open CFSG.Open (StatedSL)

section Pullback


end Pullback

section Coordinates

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {n : ℕ}


end Coordinates

section Base

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


end Base

end CFSG.ASVolI
