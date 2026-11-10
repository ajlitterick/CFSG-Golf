module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Representable
public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Connected
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Equalizer

public noncomputable section

open CategoryTheory WithConv
namespace CFSG.LieType.AlgebraicGroups

universe u v
variable {k : Type u} [Field k]

section Components
variable [IsAlgClosed k]


theorem componentPointsHom_eq_one_iff
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (x : TauCeti.HopfAlgebra.points (R := k) (H := M) (CommAlgCat.of k k)) :
    TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom M (CommAlgCat.of k k) x = 1 ↔
      TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap M x = 1 := by
  rw [TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom_apply,
    TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff,
    TauCeti.FiniteTypeCommHopfAlgCat.kernelHopfIdeal_componentCoordinateHom,
    TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap_eq_one_iff]

end Components

variable (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [Coalgebra.IsCocomm k H]

variable {W : Type u} [Group W] [Fintype W]
variable {A : Type u} [CommRing A] [Algebra k A]


@[expose] def fixedHopfIdeal (σ : H →ₐc[k] H) : TauCeti.HopfIdeal k H :=
  TauCeti.HopfIdeal.equalizer σ (BialgHom.id k H)

abbrev fixedCoordinate (σ : H →ₐc[k] H) : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k :=
  TauCeti.FiniteTypeCommHopfAlgCat.quotient H (fixedHopfIdeal H σ)

omit [Coalgebra.IsCocomm k H] in
theorem fixedCoordinateHom_comp (σ : H →ₐc[k] H) :
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom.comp σ =
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom := by
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  have hI : TauCeti.CommHopfAlgCat.equalizerHopfIdeal
      (_root_.CommHopfAlgCat.ofHom σ) (𝟙 H.obj) = fixedHopfIdeal H σ := by
    rw [TauCeti.CommHopfAlgCat.equalizerHopfIdeal_def]
    rfl
  have h := TauCeti.CommHopfAlgCat.comp_mkQuotient_equalizerHopfIdeal
    (_root_.CommHopfAlgCat.ofHom σ) (𝟙 H.obj)
  rw [hI] at h
  have h' := congrArg (fun f => f.hom) h
  change q.comp σ = q.comp (BialgHom.id k H) at h'
  simpa only [BialgHom.comp_id] using h'


omit [Coalgebra.IsCocomm k H] in
theorem fixedCoordinate_point_fixed (σ : H →ₐc[k] H)
    (x : TauCeti.HopfAlgebra.points (R := k) (H := fixedCoordinate H σ) (CommAlgCat.of k k)) :
    TauCeti.AlgHom.mapDomain σ
      (TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom x) =
      TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom x := by
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  have he : q.comp σ = q := fixedCoordinateHom_comp H σ
  change (TauCeti.AlgHom.mapDomain σ) ((TauCeti.AlgHom.mapDomain q) x) =
    (TauCeti.AlgHom.mapDomain q) x
  rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, he]


end CFSG.LieType.AlgebraicGroups
