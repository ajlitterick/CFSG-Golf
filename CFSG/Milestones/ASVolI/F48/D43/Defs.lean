module

public import CFSG.Milestones.ASVolI.F48.D43.Inputs
public import CFSG.Milestones.ASVolI.F48.Small.Pres

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Open CFSG.ASVolI.ChF

@[expose] noncomputable def burnsideF48d_perm (T : Table) : Equiv.Perm (Fin 26572) :=
  Classical.epsilon fun g => Rep 26572 T g

@[expose] noncomputable def burnsideF48d_γ (k : ℕ) : Equiv.Perm (Fin 26572) :=
  burnsideF48d_perm (burnsideF48d_toT (burnsideF48d_gen k))


@[expose] noncomputable def burnsideF48d_X : Subgroup (Equiv.Perm (Fin 26572)) :=
  Subgroup.closure (Set.range fun k : Fin 8 => burnsideF48d_γ k)


end CFSG.ASVolI
