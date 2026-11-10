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

def fixedCoordinateMap
    (M X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σM : M →ₐc[k] M) (σX : X →ₐc[k] X) (f : M.obj ⟶ X.obj)
    (hf : f.hom.comp σM = σX.comp f.hom) :
    fixedCoordinate M σM ⟶ fixedCoordinate X σX := by
  let qX := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient X (fixedHopfIdeal X σX)).hom.hom
  let g := qX.comp f.hom
  have hg : g.comp σM = g := by
    dsimp only [g]
    rw [BialgHom.comp_assoc, hf, ← BialgHom.comp_assoc]
    rw [fixedCoordinateHom_comp]
  exact TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient (fixedHopfIdeal M σM)
    (TauCeti.FiniteTypeCommHopfAlgCat.ofHom g)
    (by
      change (TauCeti.HopfIdeal.equalizer σM (BialgHom.id k M)).toIdeal ≤
        RingHom.ker g.toAlgHom.toRingHom
      exact (TauCeti.HopfIdeal.equalizer_le_ker_iff g.toAlgHom.toRingHom).2 fun x =>
        congrArg (fun h : M →ₐc[k] fixedCoordinate X σX => h x) hg)

omit [IsAlgClosed k] in
theorem fixedCoordinateMap_comp
    (M X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σM : M →ₐc[k] M) (σX : X →ₐc[k] X) (f : M.obj ⟶ X.obj)
    (hf : f.hom.comp σM = σX.comp f.hom) :
    (fixedCoordinateMap M X σM σX f hf).hom.hom.comp
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M (fixedHopfIdeal M σM)).hom.hom =
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient X (fixedHopfIdeal X σX)).hom.hom.comp
        f.hom := by
  have h := TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_comp_liftQuotient
    (fixedHopfIdeal M σM)
    (TauCeti.FiniteTypeCommHopfAlgCat.ofHom
      ((TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient X (fixedHopfIdeal X σX)).hom.hom.comp f.hom))
    (by
      let qX := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient X (fixedHopfIdeal X σX)).hom.hom
      let g := qX.comp f.hom
      have hg : g.comp σM = g := by
        dsimp only [g]
        rw [BialgHom.comp_assoc, hf, ← BialgHom.comp_assoc, fixedCoordinateHom_comp]
      change (TauCeti.HopfIdeal.equalizer σM (BialgHom.id k M)).toIdeal ≤
        RingHom.ker g.toAlgHom.toRingHom
      exact (TauCeti.HopfIdeal.equalizer_le_ker_iff g.toAlgHom.toRingHom).2 fun x =>
        congrArg (fun h : M →ₐc[k] fixedCoordinate X σX => h x) hg)
  exact congrArg TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom h


end CFSG.LieType.AlgebraicGroups
