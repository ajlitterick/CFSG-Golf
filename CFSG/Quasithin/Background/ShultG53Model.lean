module

public import CFSG.Quasithin.Background.RonanG51Lines
public import CFSG.Quasithin.Background.ShultG53Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6 CFSG.Quasithin.RonanG51 Equiv

abbrev V4 : Type := Fin 4 → ZMod 2

@[expose] def Rm (k : Fin 2) (σ : Perm (Fin 6)) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  if k = 0 then heartHom σ else heartHom (totalPermHom σ)


@[expose] def B0 (x y : V4) : ZMod 2 :=
  x 0 * y 1 + x 1 * y 0 + x 1 * y 2 + x 2 * y 1 + x 2 * y 3 + x 3 * y 2


end CFSG.Quasithin.ShultG53
