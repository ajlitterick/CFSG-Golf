module

public import CFSG.ThirdParty.TauCeti.HopfIdealNormalRationalPoint
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic

public noncomputable section
open WithConv CategoryTheory
open scoped TensorProduct
namespace CFSG.LieType.AlgebraicGroups.GradedKernel
universe u v w

section Linear
variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]


variable {G : Type w} [Group G]
variable (ρ : Representation k G V) (F : ℕ → Submodule k V)
    (hstab : ∀ g i, ∀ v ∈ F i, ρ g v ∈ F i)


end Linear

section Hopf
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced M]
variable (V : Type u) [AddCommGroup V] [Module k V] [TauCeti.Comodule k M V]
    [Module.Finite k V]
variable (F : ℕ → Submodule k V)
    (hstab : ∀ (g : WithConv (M →ₐ[k] k)) i, ∀ v ∈ F i,
      TauCeti.Comodule.basePointsRepresentation V g v ∈ F i)


omit [IsReduced M] in
theorem isUnipotentPoint_of_isNilpotent_basePointsRepresentation_sub_one
    (hV : TauCeti.Comodule.IsFaithful (k := k) (H := M) (V := V))
    (g : WithConv (M →ₐ[k] k))
    (hg : IsNilpotent (TauCeti.Comodule.basePointsRepresentation V g - 1)) :
    TauCeti.HopfAlgebra.IsUnipotentPoint g := by
  rw [TauCeti.HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
    (TauCeti.FGComoduleCat.of (R := k) (C := M) V) hV]
  rw [LinearMap.GeneralLinearGroup.isUnipotent_def]
  have hρ : TauCeti.Comodule.basePointsRepresentation (H := M) V g =
      (TensorProduct.lid k V).conjAlgEquiv k (TauCeti.Comodule.endOfPoint V g.ofConv) := by
    ext m
    rw [LinearEquiv.conjAlgEquiv_apply, TauCeti.Comodule.basePointsRepresentation_apply]
    simp
  rw [hρ] at hg
  have hn := hg.map ((TensorProduct.lid k V).conjAlgEquiv k).symm
  rw [map_sub, map_one, AlgEquiv.symm_apply_apply] at hn
  convert hn using 2
  exact TauCeti.Comodule.pointsAction_toLinearMap (V := V) g


end Hopf


end CFSG.LieType.AlgebraicGroups.GradedKernel
