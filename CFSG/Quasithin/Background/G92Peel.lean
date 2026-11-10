module

public import CFSG.Quasithin.Background.G92Lin

public section

namespace CFSG.Quasithin.G92

open CFSG.Quasithin.SzN31 CFSG.Quasithin.SzN31.CntLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ι : Type}


@[expose] def Wsp (F : Frame V ι) (i : ι) : Submodule (ZMod 2) V :=
  fixSp V (F.a i) (commSp V (F.x i) ⊤)


section Basic


end Basic

section StepA


end StepA

section Blocks


end Blocks


section Main


end Main

end CFSG.Quasithin.G92
