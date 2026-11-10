module

public import CFSG.LieType.AlgebraicGroups.FixedComponentNorm
public import CFSG.GroupTheory.FixedCentralDefect
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer

public noncomputable section

open CategoryTheory WithConv
namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem fixedCoordinate_points_range
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : M →ₐc[k] M) :
    (TauCeti.AlgHom.mapDomain (A := k)
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M (fixedHopfIdeal M σ)).hom.hom).range =
      TauCeti.fixedSubgroup (TauCeti.AlgHom.mapDomain (A := k) σ) := by
  ext x
  change x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj (fixedHopfIdeal M σ)
    (CommAlgCat.of k k) ↔ TauCeti.AlgHom.mapDomain σ x = x
  have hI : TauCeti.CommHopfAlgCat.equalizerHopfIdeal
      (_root_.CommHopfAlgCat.ofHom σ) (𝟙 M.obj) = fixedHopfIdeal M σ := by
    rw [TauCeti.CommHopfAlgCat.equalizerHopfIdeal_def]
    rfl
  rw [← hI, TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_equalizerHopfIdeal_iff]
  change TauCeti.AlgHom.mapDomain σ x =
      TauCeti.AlgHom.mapDomain (BialgHom.id k M) x ↔ _
  rw [TauCeti.AlgHom.mapDomain_id, MonoidHom.id_apply]


end CFSG.LieType.AlgebraicGroups
