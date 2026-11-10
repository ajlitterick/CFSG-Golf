module

public import CFSG.Quasithin.Background.ShultG53Layers
public import CFSG.Quasithin.Background.ShultG53CoverData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6 CFSG.Quasithin.RonanG51 Equiv

@[expose] def inLine : Fin 2 → V4 → Prop
  | 0 => fun y => y = 0 ∨ y = ![1, 0, 0, 0] ∨ y = ![0, 0, 1, 0] ∨ y = ![1, 0, 1, 0]
  | 1 => fun y => y = 0 ∨ y = ![1, 0, 0, 0] ∨ y = ![0, 0, 1, 1] ∨ y = ![1, 0, 1, 1]

instance (k : Fin 2) (y : V4) : Decidable (inLine k y) :=
  match k with
  | 0 => inferInstanceAs (Decidable
      (y = 0 ∨ y = ![1, 0, 0, 0] ∨ y = ![0, 0, 1, 0] ∨ y = ![1, 0, 1, 0]))
  | 1 => inferInstanceAs (Decidable
      (y = 0 ∨ y = ![1, 0, 0, 0] ∨ y = ![0, 0, 1, 1] ∨ y = ![1, 0, 1, 1]))


end CFSG.Quasithin.ShultG53
