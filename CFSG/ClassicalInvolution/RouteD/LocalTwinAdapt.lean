module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinWeyl
public import CFSG.ClassicalInvolution.RouteD.LocalTwinModel
public import CFSG.ClassicalInvolution.RouteD.GapsAut
public import CFSG.ClassicalInvolution.RouteD.LocalTwinDict
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (conjSub modelUniv centralizingMembers ConjInvariant)

variable {p f : ℕ} [Fact p.Prime]

theorem map_conj_map_hom {X Y : Type*} [Group X] [Group Y] (ψ : X →* Y) (k : X) (S : Subgroup X) :
    (S.map ψ).map (MulAut.conj (ψ k)).toMonoidHom = (conjSub k S).map ψ := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext s
  simp [MulAut.conj_apply, map_mul, map_inv]


namespace TCtx


end TCtx

end CFSG.ClassicalInvolution.RouteD
