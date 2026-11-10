module

public import CFSG.CharacterTheory.TwoRankLowerBound.PGroupInvariantSum
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem monoidAlgebra_basis_repr_coeff {ring points : Type*} [CommRing ring]
    (value : MonoidAlgebra ring points) (point : points) :
    ((MonoidAlgebra.basis points ring).repr value) point = value.coeff point := by
  rfl

@[expose] def permutationMapEquivariant {ring group source target : Type*}
    [CommRing ring] [Group group] [MulAction group source] [MulAction group target]
    (operator : MonoidAlgebra ring source →ₗ[ring] MonoidAlgebra ring target) : Prop :=
  ∀ element : group,
    operator.comp (Representation.ofMulAction ring group source element) =
      (Representation.ofMulAction ring group target element).comp operator


theorem permutationMapEquivariant_of_commute {ring group points : Type*}
    [CommRing ring] [Group group] [MulAction group points]
    (operator : Module.End ring (MonoidAlgebra ring points))
    (hcommute : ∀ element : group, Commute operator (Representation.ofMulAction ring group points element)) :
    permutationMapEquivariant (group := group) operator := fun element => (hcommute element).eq

theorem permutationMapEquivariant_coeff {ring group source target : Type*}
    [CommRing ring] [Group group] [MulAction group source] [MulAction group target]
    (operator : MonoidAlgebra ring source →ₗ[ring] MonoidAlgebra ring target)
    (hequivariant : permutationMapEquivariant (group := group) operator)
    (element : group) (row : target) (column : source) :
    (operator (MonoidAlgebra.single (element • column) 1)).coeff (element • row) =
      (operator (MonoidAlgebra.single column 1)).coeff row := by
  have hequal := congrArg
    (fun value : MonoidAlgebra ring source →ₗ[ring] MonoidAlgebra ring target =>
      (value (MonoidAlgebra.single column 1)).coeff (element • row)) (hequivariant element)
  simpa only [LinearMap.comp_apply, Representation.ofMulAction_single,
    Representation.coeff_ofMulAction, inv_smul_smul] using hequal

theorem permutationLinearMap_comp_coeff {ring source middle target : Type*}
    [CommRing ring] [Fintype source] [Fintype middle] [Fintype target]
    (left : MonoidAlgebra ring middle →ₗ[ring] MonoidAlgebra ring target)
    (right : MonoidAlgebra ring source →ₗ[ring] MonoidAlgebra ring middle)
    (row : target) (column : source) :
    ((left.comp right) (MonoidAlgebra.single column 1)).coeff row =
      ∑ member : middle, (left (MonoidAlgebra.single member 1)).coeff row *
        (right (MonoidAlgebra.single column 1)).coeff member := by
  have hequal := congrArg (fun matrix : Matrix target source ring => matrix row column)
    (LinearMap.toMatrix_comp (MonoidAlgebra.basis source ring) (MonoidAlgebra.basis middle ring)
      (MonoidAlgebra.basis target ring) left right)
  simpa only [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    monoidAlgebra_basis_repr_coeff, Matrix.mul_apply] using hequal

@[expose] noncomputable def permutationFixedBasisReduction {ring residue group source target : Type*}
    [CommRing ring] [CommRing residue] [Group group]
    [MulAction group source] [MulAction group target] [Fintype source] [Fintype target]
    (embedding : ring →+* residue)
    (operator : MonoidAlgebra ring source →ₗ[ring] MonoidAlgebra ring target) :
    MonoidAlgebra residue (MulAction.fixedPoints group source) →ₗ[residue]
      MonoidAlgebra residue (MulAction.fixedPoints group target) :=
  Matrix.toLin (MonoidAlgebra.basis (MulAction.fixedPoints group source) residue)
    (MonoidAlgebra.basis (MulAction.fixedPoints group target) residue)
    (fun row column => embedding ((operator (MonoidAlgebra.single column.val 1)).coeff row.val))

theorem permutationFixedBasisReduction_matrix {ring residue group source target : Type*}
    [CommRing ring] [CommRing residue] [Group group]
    [MulAction group source] [MulAction group target] [Fintype source] [Fintype target]
    (embedding : ring →+* residue)
    (operator : MonoidAlgebra ring source →ₗ[ring] MonoidAlgebra ring target) :
    LinearMap.toMatrix (MonoidAlgebra.basis (MulAction.fixedPoints group source) residue)
      (MonoidAlgebra.basis (MulAction.fixedPoints group target) residue)
      (permutationFixedBasisReduction (group := group) embedding operator) =
        fun row column => embedding ((operator (MonoidAlgebra.single column.val 1)).coeff row.val) := by
  exact LinearMap.toMatrix_toLin _ _ _

theorem permutationFixedBasisReduction_coeff {ring residue group source target : Type*}
    [CommRing ring] [CommRing residue] [Group group]
    [MulAction group source] [MulAction group target] [Fintype source] [Fintype target]
    (embedding : ring →+* residue)
    (operator : MonoidAlgebra ring source →ₗ[ring] MonoidAlgebra ring target)
    (row : MulAction.fixedPoints group target) (column : MulAction.fixedPoints group source) :
    ((permutationFixedBasisReduction (group := group) embedding operator)
      (MonoidAlgebra.single column 1)).coeff row =
      embedding ((operator (MonoidAlgebra.single column.val 1)).coeff row.val) := by
  have hequal := congrArg
    (fun matrix : Matrix (MulAction.fixedPoints group target) (MulAction.fixedPoints group source) residue =>
      matrix row column) (permutationFixedBasisReduction_matrix embedding operator)
  simpa only [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    monoidAlgebra_basis_repr_coeff] using hequal


theorem permutationFixedBasisReduction_comp {ring residue group source middle target : Type*}
    [CommRing ring] [CommRing residue] [Group group] [Finite group]
    [MulAction group source] [MulAction group middle] [MulAction group target]
    [Fintype source] [Fintype middle] [Fintype target]
    (embedding : ring →+* residue) (prime : ℕ) [Fact prime.Prime] [CharP residue prime]
    (hgroup : IsPGroup prime group)
    (left : MonoidAlgebra ring middle →ₗ[ring] MonoidAlgebra ring target)
    (right : MonoidAlgebra ring source →ₗ[ring] MonoidAlgebra ring middle)
    (hleft : permutationMapEquivariant (group := group) left)
    (hright : permutationMapEquivariant (group := group) right) :
    permutationFixedBasisReduction (group := group) embedding (left.comp right) =
      (permutationFixedBasisReduction (group := group) embedding left).comp
        (permutationFixedBasisReduction (group := group) embedding right) := by
  apply (MonoidAlgebra.basis (MulAction.fixedPoints group source) residue).ext
  intro column
  ext row
  simp only [MonoidAlgebra.basis_apply, permutationFixedBasisReduction_coeff,
    permutationLinearMap_comp_coeff, map_sum, map_mul]
  have hinvariant : ∀ (element : group) (member : middle),
      embedding ((left (MonoidAlgebra.single (element • member) 1)).coeff row.val) *
        embedding ((right (MonoidAlgebra.single column.val 1)).coeff (element • member)) =
      embedding ((left (MonoidAlgebra.single member 1)).coeff row.val) *
        embedding ((right (MonoidAlgebra.single column.val 1)).coeff member) := by
    intro element member
    have hrow := MulAction.mem_fixedPoints.mp row.property element
    have hcolumn := MulAction.mem_fixedPoints.mp column.property element
    have hleftCoeff := permutationMapEquivariant_coeff left hleft element row.val member
    have hrightCoeff := permutationMapEquivariant_coeff right hright element member column.val
    rw [hrow] at hleftCoeff
    rw [hcolumn] at hrightCoeff
    rw [hleftCoeff, hrightCoeff]
  rw [p_group_invariant_sum_fixedPoints prime hgroup _ hinvariant]
  rw [← Finset.sum_filter]
  apply Finset.sum_subtype
  intro member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]


end CFSG.TwoRankLowerBound.Helpers
