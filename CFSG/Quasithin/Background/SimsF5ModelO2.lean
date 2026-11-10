module

public import CFSG.Quasithin.Background.SimsF5Par
public import CFSG.Quasithin.Background.SimsF5Lin

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open scoped Pointwise


instance o2_Q2Dot_normal_inst : (Q2Dot.subgroupOf M2Dot).Normal := Q2Dot_normal


end

end CFSG.Quasithin.SimsF5
