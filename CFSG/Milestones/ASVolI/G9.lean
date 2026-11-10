module

public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.Milestones.ASVolI.G4
public import CFSG.Quasithin.Background.Harris.Holds
import CFSG.Quasithin.Background.G9A8OrthModule
import CFSG.Quasithin.Background.SzG11G94Final
import CFSG.Quasithin.Background.G92Main

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Assembly.LowTwoRank


section

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]


end


section Cases

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]


@[expose] def IsSubSD16Heis (Γ : Subgroup (GLV V)) : Prop :=
  CFSG.Quasithin.IsSubSD16Heis Γ

end Cases

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG CFSG.Assembly.LowTwoRank
open scoped commutatorElement


section as_G_9_3


end as_G_9_3


section SmallZero


end SmallZero


end CFSG.ASVolI
