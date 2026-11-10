module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalElementary
public import Mathlib.Algebra.Field.ZMod

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace SingularPlaneRoots

open Module QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide


@[expose] def rootMap (u v : V) : V →ₗ[ZMod 2] V :=
  LinearMap.id + (polarBilin q v).smulRight u + (polarBilin q u).smulRight v


@[expose] def rootSet : Set (V ≃ₗ[ZMod 2] V) :=
  {s | s ∈ TauCeti.QuadraticMap.orthogonalGroup q ∧ s * s = 1 ∧
    finrank (ZMod 2) (LinearMap.range ((s : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2 ∧
    ∀ x ∈ LinearMap.range ((s : V →ₗ[ZMod 2] V) - LinearMap.id), q x = 0}


theorem mem_rootSet {s : V ≃ₗ[ZMod 2] V} :
    s ∈ rootSet q ↔ s ∈ TauCeti.QuadraticMap.orthogonalGroup q ∧ s * s = 1 ∧
      finrank (ZMod 2) (LinearMap.range ((s : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2 ∧
      ∀ x ∈ LinearMap.range ((s : V →ₗ[ZMod 2] V) - LinearMap.id), q x = 0 :=
  Iff.rfl


end SingularPlaneRoots

section Transpositions

variable {A : Type*} [Group A]

@[expose] def IsThreeFourPlusTranspositions (D : Set A) : Prop :=
  (∀ g : A, ∀ x ∈ D, g * x * g⁻¹ ∈ D) ∧ (∀ x ∈ D, orderOf x = 2) ∧ Subgroup.closure D = ⊤ ∧
    (∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) ≤ 4) ∧
    ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) = 4 → x * y * x⁻¹ * y⁻¹ ∈ D

@[expose] def IsThreeTranspositions (D : Set A) : Prop :=
  IsThreeFourPlusTranspositions D ∧ ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) ≤ 3

end Transpositions


end CFSG.LocalAnalysis.GorensteinLyons
