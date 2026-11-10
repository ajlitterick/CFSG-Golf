module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Map
public import TauCeti.LinearAlgebra.End.FiniteOrder
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint
public import TauCeti.RingTheory.FiniteType.PointSeparation

public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k]

section Coalgebra
variable {C : Type u} [AddCommGroup C] [Module k C] [Coalgebra k C]

def cyclicClosureThree (f : C →ₗc[k] C) (D : TauCeti.Subcoalgebra k C) :
    TauCeti.Subcoalgebra k C := D ⊔ D.map f ⊔ D.map (f.comp f)

theorem le_cyclicClosureThree (f : C →ₗc[k] C) (D : TauCeti.Subcoalgebra k C) :
    D ≤ cyclicClosureThree f D := le_sup_left.trans le_sup_left

theorem map_cyclicClosureThree (f : C →ₗc[k] C)
    (hf : (f.comp f).comp f = CoalgHom.id k C) (D : TauCeti.Subcoalgebra k C) :
    (cyclicClosureThree f D).map f = cyclicClosureThree f D := by
  have hf' : f.comp (f.comp f) = CoalgHom.id k C := by
    simpa only [CoalgHom.comp_assoc] using hf
  simp only [cyclicClosureThree, TauCeti.Subcoalgebra.map_sup,
    TauCeti.Subcoalgebra.map_map, hf', TauCeti.Subcoalgebra.map_id]
  ac_rfl

theorem finite_cyclicClosureThree (f : C →ₗc[k] C) (D : TauCeti.Subcoalgebra k C)
    [Module.Finite k D.toSubmodule] :
    Module.Finite k (cyclicClosureThree f D).toSubmodule := by
  let : Module.Finite k (D.map f).toSubmodule := TauCeti.Subcoalgebra.map_finite f D
  let : Module.Finite k (D.map (f.comp f)).toSubmodule := TauCeti.Subcoalgebra.map_finite _ D
  let : Module.Finite k (D ⊔ D.map f).toSubmodule := TauCeti.Subcoalgebra.sup_finite _ _
  exact TauCeti.Subcoalgebra.sup_finite _ _

end Coalgebra

section PointAction

variable {H : Type u} [CommRing H] [HopfAlgebra k H]
variable {M N : Type u} [AddCommMonoid M] [Module k M] [TauCeti.Comodule k H M]
variable [AddCommMonoid N] [Module k N] [TauCeti.Comodule k H N]


end PointAction

section CoefficientMatrix

variable {H M : Type u} [CommRing H] [HopfAlgebra k H]
variable [AddCommMonoid M] [Module k M] [TauCeti.Comodule k H M]

theorem pointsMulEquiv_coordinateBialgHom_eq_toMatrix
    {n : ℕ} (b : Module.Basis (Fin n) k M) (g : WithConv (H →ₐ[k] k)) :
    (TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain (TauCeti.Comodule.coordinateBialgHom (H := H) b) g) :
      Matrix (Fin n) (Fin n) k) =
    LinearMap.toMatrixAlgEquiv b
      (TauCeti.Comodule.basePointsRepresentation (H := H) M g) := by
  rw [TauCeti.AlgHom.mapDomain_apply, AlgHom.pointsMulEquiv_comp_coordinateBialgHom]
  ext i j
  rw [Matrix.map_apply, TauCeti.Comodule.coefficientMatrix_apply,
    LinearMap.toMatrixAlgEquiv_apply]
  exact TauCeti.Comodule.apply_matrixCoefficient g (b.coord i) (b j)

end CoefficientMatrix

theorem isSemisimplePoint_of_pow_eq_one
    {K H : Type u} [CommRing H] [HopfAlgebra k H]
    [Field K] [Algebra k K] (g : WithConv (H →ₐ[k] K)) {n : ℕ}
    (hn : (n : K) ≠ 0) (hg : g ^ n = 1) :
    TauCeti.HopfAlgebra.IsSemisimplePoint g := by
  apply (TauCeti.HopfAlgebra.isSemisimplePoint_iff_forall_isSemisimple_endOfPoint g).mpr
  intro M
  apply TauCeti.End.isSemisimple_of_pow_eq_one hn
  have h := congrArg
    (TauCeti.Comodule.pointsRepresentation (R := k) (H := H) (A := K) M) hg
  simpa only [map_pow, map_one, TauCeti.Comodule.pointsRepresentation_apply] using h

theorem basePointsRepresentation_injective_of_generating_subcoalgebra
    {H : Type u} [CommRing H] [HopfAlgebra k H]
    (D : TauCeti.Subcoalgebra k H) (hgen : Algebra.adjoin k (D : Set H) = ⊤) :
    Function.Injective
      (TauCeti.Comodule.basePointsRepresentation (R := k) (H := H) D.toRegularSubcomodule) := by
  intro g h heq
  apply WithConv.ext
  apply AlgHom.ext_of_adjoin_eq_top hgen
  intro x hx
  let φ : Module.Dual k D.toRegularSubcomodule :=
    (Coalgebra.counit (R := k) (A := H)).comp (SMulMemClass.subtype D.toRegularSubcomodule)
  have hcoeff : TauCeti.Comodule.matrixCoefficient (C := H) φ
      (⟨x, hx⟩ : D.toRegularSubcomodule) = x := by
    exact TauCeti.Comodule.matrixCoefficient_counit_comp_subtype D.toRegularSubcomodule ⟨x, hx⟩
  have hg := TauCeti.Comodule.apply_matrixCoefficient g φ (⟨x, hx⟩ : D.toRegularSubcomodule)
  have hh := TauCeti.Comodule.apply_matrixCoefficient h φ (⟨x, hx⟩ : D.toRegularSubcomodule)
  rw [hcoeff] at hg hh
  rw [hg, hh, heq]


section LinearActor
variable {H : Type u} [CommRing H] [HopfAlgebra k H] (σ : H →ₐc[k] H)
variable (hσ : (σ.comp σ).comp σ = BialgHom.id k H)
variable (D : TauCeti.Subcoalgebra k H) (hD : D.map σ.toCoalgHom = D)

local instance : AddCommGroup D.toRegularSubcomodule :=
  Module.addCommMonoidToAddCommGroup k


end LinearActor

theorem coordinateBialgHom_surjective_of_generating_subcoalgebra
    {H : Type u} [CommRing H] [HopfAlgebra k H]
    (D : TauCeti.Subcoalgebra k H) (hgen : Algebra.adjoin k (D : Set H) = ⊤)
    {n : ℕ} (b : Module.Basis (Fin n) k D.toRegularSubcomodule) :
    Function.Surjective (TauCeti.Comodule.coordinateBialgHom (H := H) b) := by
  have hcoeff : TauCeti.Comodule.matrixCoefficientSubalgebra (R := k) (C := H)
      (M := D.toRegularSubcomodule) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact Algebra.adjoin_le fun x hx => D.le_matrixCoefficientSubalgebra_toRegularSubcomodule hx
  change Function.Surjective (TauCeti.Comodule.coordinateBialgHom (H := H) b).toAlgHom
  rw [← AlgHom.range_eq_top]
  apply top_unique
  rw [← hcoeff]
  exact TauCeti.Comodule.matrixCoefficientSubalgebra_le_coordinateBialgHom_range b

theorem exists_finite_invariant_generating_subcoalgebra_three
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : H →ₐc[k] H)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    ∃ D : TauCeti.Subcoalgebra k H,
      Module.Finite k D.toSubmodule ∧ D.map σ.toCoalgHom = D ∧
        Algebra.adjoin k (D : Set H) = ⊤ := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k H).out
  obtain ⟨D, hD, hsD⟩ := TauCeti.Subcoalgebra.exists_finiteDimensional_subcoalgebra_of_setFinite
    (k := k) (C := H) (s : Set H) s.finite_toSet
  let : Module.Finite k D.toSubmodule := hD
  let E := cyclicClosureThree σ.toCoalgHom D
  have hc : (σ.toCoalgHom.comp σ.toCoalgHom).comp σ.toCoalgHom = CoalgHom.id k H :=
    congrArg BialgHom.toCoalgHom hσ
  refine ⟨E, finite_cyclicClosureThree _ _, map_cyclicClosureThree _ hc _, ?_⟩
  apply top_unique
  rw [← hs]
  apply Algebra.adjoin_mono
  intro x hx
  exact le_cyclicClosureThree σ.toCoalgHom D (hsD hx)

structure SemisimpleAffineCoordinatesThree
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : H →ₐc[k] H) where
  coalgebra : TauCeti.Subcoalgebra k H
  finite : Module.Finite k coalgebra.toSubmodule
  invariant : coalgebra.map σ.toCoalgHom = coalgebra
  generates : Algebra.adjoin k (coalgebra : Set H) = ⊤
  dimension : ℕ
  basis : Module.Basis (Fin dimension) k coalgebra.toRegularSubcomodule
  coordinateSurjective :
    Function.Surjective (TauCeti.Comodule.coordinateBialgHom (H := H) basis)
  actor : coalgebra.toRegularSubcomodule ≃ₗ[k] coalgebra.toRegularSubcomodule
  actor_cube : actor.toLinearMap ^ 3 = 1
  actor_semisimple :
    letI : AddCommGroup coalgebra.toRegularSubcomodule := Module.addCommMonoidToAddCommGroup k
    Module.End.IsSemisimple actor.toLinearMap
  actor_conj : ∀ g : WithConv (H →ₐ[k] k),
    TauCeti.Comodule.basePointsRepresentation (H := H) coalgebra.toRegularSubcomodule
        (TauCeti.AlgHom.mapDomain σ g) =
      actor.symm.toLinearMap ∘ₗ
        TauCeti.Comodule.basePointsRepresentation (H := H) coalgebra.toRegularSubcomodule g ∘ₗ
        actor.toLinearMap


namespace SemisimpleAffineCoordinatesThree

variable {H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {σ : H →ₐc[k] H}
variable (E : SemisimpleAffineCoordinatesThree H σ)


local instance : AddCommGroup E.coalgebra.toRegularSubcomodule :=
  Module.addCommMonoidToAddCommGroup k

local instance : Module.Finite k E.coalgebra.toSubmodule := E.finite

local instance : Module.Finite k E.coalgebra.toRegularSubcomodule :=
  E.coalgebra.toRegularSubcomodule_finite


end SemisimpleAffineCoordinatesThree

end CFSG.LieType.AlgebraicGroups
