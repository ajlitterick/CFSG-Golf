module

public import CFSG.Milestones.ASVolI.C135.P2
public import CFSG.Milestones.ASVolI.C135.N1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL specialLinearGroupEquivStatedSL_coe)
open CFSG.Quasithin.H13.Ch4.C135 (slNat dualHom coe_dualHom coe_slNat moduleAct_false_eq
  moduleAct_true_eq)
open scoped Matrix commutatorElement

variable {G : Type} [Group G]


section Case3

variable [Finite G] {L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)}

@[expose] def burnsideC135_proj (F : Type) [Field F] (i : Fin 2) :
    Multiplicative (Fin 2 → Fin 3 → F) →* Multiplicative (Fin 3 → F) :=
  AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ => Fin 3 → F) i)


end Case3

end CFSG.ASVolI

end
