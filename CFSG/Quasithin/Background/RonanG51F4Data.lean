module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.GoldschmidtG52Finite

public section

namespace CFSG.Quasithin.RonanG51

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix FieldFour
  CFSG.Quasithin.H13.A6.G52 Matrix Equiv

@[expose] def basis8' : Matrix (Fin 16) (Fin 8) FieldFour := basis8.map frob

@[expose] def proj8' : Matrix (Fin 8) (Fin 16) FieldFour := proj8.map frob


end CFSG.Quasithin.RonanG51
