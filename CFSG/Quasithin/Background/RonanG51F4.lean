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

noncomputable def B2 : Matrix (Fin 16) (Fin 8) F4 := basis8'.map φ

noncomputable def P1 : Matrix (Fin 8) (Fin 16) F4 := proj8.map φ

noncomputable def P2 : Matrix (Fin 8) (Fin 16) F4 := proj8'.map φ


section Tensor

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (e : V ≃ₗ[ZMod 2] (Fin 16 → ZMod 2))

noncomputable def U1 : Submodule F4 (F4 ⊗[ZMod 2] V) :=
  (LinearMap.range (Matrix.mulVecLin B1)).comap (theta F4 e).toLinearMap

noncomputable def U2 : Submodule F4 (F4 ⊗[ZMod 2] V) :=
  (LinearMap.range (Matrix.mulVecLin B2)).comap (theta F4 e).toLinearMap


end Tensor


end CFSG.Quasithin.RonanG51
