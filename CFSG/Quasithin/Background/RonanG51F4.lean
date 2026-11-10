module

public import CFSG.Quasithin.Background.RonanG51F4Data
public import CFSG.Quasithin.Background.RonanG51Tensor
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.RonanG51

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix FieldFour
  CFSG.Quasithin.H13.A6.G52 Matrix Equiv
open scoped TensorProduct

abbrev F4 : Type := GaloisField 2 2

noncomputable def ι : FieldFour ≃ₐ[ZMod 2] F4 :=
  GaloisField.algEquivGaloisField 2 2 (by simpa using natCard_eq)

noncomputable def φ : FieldFour →+* F4 := (ι : FieldFour →+* F4)


noncomputable def B1 : Matrix (Fin 16) (Fin 8) F4 := basis8.map φ


section Tensor


end Tensor


end CFSG.Quasithin.RonanG51
