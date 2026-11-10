module

public import CFSG.Milestones.ASVolI.I2
public import CFSG.Milestones.ASVolI.B4G2
public import CFSG.Quasithin.Recognition.HSTypeConj
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Rk
public import CFSG.Quasithin.MS93.M15WeylQ

public section

namespace CFSG.ASVolI

open CFSG.Open

section Basic

variable {W : Type} [CommGroup W]


end Basic

section Restr

open CFSG.Quasithin

variable {W : Type} [CommGroup W] {M : Type} [CommGroup M]


end Restr

section Model

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8

variable {K : Type} [Field K] [CharP K 2] [Finite K]


end Model

section Aux

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


noncomputable local instance burnsideI17b_algZ2 (K : Type) [Field K] [CharP K 2] :
    Algebra (ZMod 2) K := ZMod.algebra K 2


end Aux

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in

section DualStmts

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8


open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.MS93 in

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in


end DualStmts

section One

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.H13
  CFSG.Quasithin.H13.VolI in


end One

section One2

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.H13
  CFSG.Quasithin.Vol2.Ch11.G2Q8


end One2

section Main

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8


end Main

section Final


end Final

end CFSG.ASVolI
