module

public import CFSG.Milestones.ASVolI.G4
public import CFSG.Blueprint.SourceBinaryGolayCode
import CFSG.Quasithin.Background.RonanG72Sporadic
import CFSG.Quasithin.Background.RonanG73Spor
import CFSG.Quasithin.Background.RonanG73Odd
import CFSG.Quasithin.Background.RonanG73Alt7

public section

namespace CFSG.ASVolI.ChG


end CFSG.ASVolI.ChG

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11


end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG


section G71Aux

open scoped Classical

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


private instance g71_finite_glv : Finite (GLV V) :=
  Finite.of_injective (fun e : GLV V => (e : V → V))
    fun _ _ h => LinearEquiv.ext fun x => congrFun h x

private noncomputable instance g71_fintype_glv : Fintype (GLV V) := Fintype.ofFinite _

private instance g71_finite_subgroup : Finite (Subgroup (GLV V)) :=
  Finite.of_injective (fun H : Subgroup (GLV V) => (H : Set (GLV V))) SetLike.coe_injective

private instance g71_finite_submodule : Finite (Submodule (ZMod 2) V) :=
  Finite.of_injective (fun W : Submodule (ZMod 2) V => (W : Set V)) SetLike.coe_injective


end G71Aux


section G72


end G72


section G73


end G73

end CFSG.ASVolI
