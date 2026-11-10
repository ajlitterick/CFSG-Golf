module

public import CFSG.Quasithin.Background.G12Final
public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open

section Vocab

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]


end Vocab

section Hat

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Û : Type} [AddCommGroup Û] [Module (ZMod 2) Û]


end Hat

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.ASVolI.ChG


private instance g12h2_finite_glv {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Finite (GLV V) :=
  Finite.of_injective _ DFunLike.coe_injective


end CFSG.ASVolI
