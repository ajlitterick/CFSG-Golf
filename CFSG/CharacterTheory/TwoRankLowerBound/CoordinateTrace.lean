module

public import CFSG.CharacterTheory.TwoRankLowerBound.GroupAlgebraUnitResidue
public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteSummandCoordinates

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def supportedCoordinatesEquiv {ring index : Type*} [Ring ring]
    (vector : index → Type*) [∀ label, AddCommGroup (vector label)]
    [∀ label, Module ring (vector label)] (support : Set index) :
    supportedCoordinateSubmodule (ring := ring) vector support ≃ₗ[ring]
      (∀ label : support, vector label.val) where
  toFun := fun value label => value.val label.val
  invFun := fun value => ⟨fun label => if hmember : label ∈ support then value ⟨label, hmember⟩ else 0,
    fun label hnot => dite_eq_right hnot⟩
  left_inv := by
    intro value
    apply Subtype.ext
    funext label
    by_cases hmember : label ∈ support
    · simp only [dite_eq_left hmember]
    · simpa only [dite_eq_right hmember] using (value.property label hmember).symm
  right_inv := by
    intro value
    funext label
    simp only [dite_eq_left label.property]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[expose] noncomputable def coordinatewiseEndomorphism {ring index : Type*} [Semiring ring]
    (vector : index → Type*) [∀ label, AddCommMonoid (vector label)]
    [∀ label, Module ring (vector label)] (operator : ∀ label, Module.End ring (vector label)) :
    Module.End ring (∀ label, vector label) :=
  LinearMap.pi (fun label => (operator label).comp (LinearMap.proj label))

theorem coordinatewiseEndomorphism_apply {ring index : Type*} [Semiring ring]
    (vector : index → Type*) [∀ label, AddCommMonoid (vector label)]
    [∀ label, Module ring (vector label)] (operator : ∀ label, Module.End ring (vector label))
    (value : ∀ label, vector label) (label : index) :
    coordinatewiseEndomorphism vector operator value label = operator label (value label) := rfl

theorem coordinatewiseEndomorphism_trace {ring index : Type*} [CommRing ring] [Fintype index]
    (vector : index → Type*) [∀ label, AddCommGroup (vector label)]
    [∀ label, Module ring (vector label)] [∀ label, Module.Free ring (vector label)]
    [∀ label, Module.Finite ring (vector label)]
    (operator : ∀ label, Module.End ring (vector label)) :
    LinearMap.trace ring (∀ label, vector label) (coordinatewiseEndomorphism vector operator) =
      ∑ label, LinearMap.trace ring (vector label) (operator label) := by
  have hexpansion : coordinatewiseEndomorphism vector operator =
      ∑ label, (LinearMap.single ring vector label).comp
        ((operator label).comp (LinearMap.proj label)) := by
    apply LinearMap.ext
    intro value
    funext label
    simp [LinearMap.sum_apply, coordinatewiseEndomorphism_apply]
  rw [hexpansion, map_sum]
  apply Finset.sum_congr rfl
  intro label _
  rw [LinearMap.trace_comp_comm']
  congr 1
  apply LinearMap.ext
  intro value
  simp


theorem groupAlgebra_leftMultiplication_trace {ring group : Type*} [CommRing ring]
    [Group group] [Finite group] (value : MonoidAlgebra ring group) :
    LinearMap.trace ring (MonoidAlgebra ring group)
      (Algebra.lmul ring (MonoidAlgebra ring group) value) = Nat.card group • value.coeff 1 := by
  let := Fintype.ofFinite group
  rw [LinearMap.trace_eq_matrix_trace ring (MonoidAlgebra.basis group ring), Matrix.trace]
  change (∑ element : group, LinearMap.toMatrix (MonoidAlgebra.basis group ring)
    (MonoidAlgebra.basis group ring) (Algebra.lmul ring (MonoidAlgebra ring group) value)
    element element) = _
  simp only [groupAlgebra_leftMultiplicationMatrix_apply, mul_inv_cancel]
  simp [Nat.card_eq_fintype_card]

theorem groupAlgebra_nonidentity_translation_trace {ring group : Type*} [CommRing ring]
    [Group group] [Finite group] (element : group) (hnonidentity : element ≠ 1) :
    LinearMap.trace ring (MonoidAlgebra ring group)
      (Algebra.lmul ring (MonoidAlgebra ring group) (MonoidAlgebra.single element 1)) = 0 := by
  rw [groupAlgebra_leftMultiplication_trace]
  simp [MonoidAlgebra.coeff_single, Ne.symm hnonidentity]

end CFSG.TwoRankLowerBound.Helpers
