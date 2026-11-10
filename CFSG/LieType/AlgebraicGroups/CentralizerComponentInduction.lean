module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang
public import TauCeti.GroupTheory.Elementary

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint WithConv
  Topology

variable {τ : Tag} {k : Type} [Field k]

theorem closedIdentityComponent_mono {H K : Subgroup (ModGL τ k)} (hHK : H ≤ K) :
    closedIdentityComponent H ≤ closedIdentityComponent K := by
  refine subset_closedIdentityComponent ?_ (closedIdentityComponent H).one_mem
    (isPointIrreducible_closedIdentityComponent H)
  exact (closedIdentityComponent_le H).trans hHK


end CFSG.LieType.AlgebraicGroups

end
