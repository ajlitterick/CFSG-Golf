module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

universe fieldUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]

def projectiveLinearAction :
    (VectorType ≃ₗ[FieldType] VectorType) →* Equiv.Perm (Projectivization FieldType VectorType) where
  toFun automorphism := {
    toFun := Projectivization.map automorphism.toLinearMap automorphism.injective
    invFun := Projectivization.map automorphism.symm.toLinearMap automorphism.symm.injective
    left_inv := by
      intro point
      have composition : automorphism.symm.toLinearMap ∘ₗ automorphism.toLinearMap = LinearMap.id := by
        ext vector
        exact automorphism.symm_apply_apply vector
      have mapped := congrFun (Projectivization.map_comp automorphism.toLinearMap automorphism.injective
        automorphism.symm.toLinearMap automorphism.symm.injective) point
      simpa only [composition, Projectivization.map_id, Function.comp_apply, id_eq] using mapped.symm
    right_inv := by
      intro point
      have composition : automorphism.toLinearMap ∘ₗ automorphism.symm.toLinearMap = LinearMap.id := by
        ext vector
        exact automorphism.apply_symm_apply vector
      have mapped := congrFun (Projectivization.map_comp automorphism.symm.toLinearMap
        automorphism.symm.injective automorphism.toLinearMap automorphism.injective) point
      simpa only [composition, Projectivization.map_id, Function.comp_apply, id_eq] using mapped.symm }
  map_one' := by
    apply Equiv.ext
    intro point
    change Projectivization.map (1 : VectorType ≃ₗ[FieldType] VectorType).toLinearMap
      (1 : VectorType ≃ₗ[FieldType] VectorType).injective point = point
    simpa only [LinearEquiv.coe_toLinearMap_one, id_eq] using
      congrFun (Projectivization.map_id (K := FieldType) (V := VectorType)) point
  map_mul' first second := by
    apply Equiv.ext
    intro point
    change Projectivization.map (first * second).toLinearMap (first * second).injective point =
      Projectivization.map first.toLinearMap first.injective
        (Projectivization.map second.toLinearMap second.injective point)
    exact congrFun (Projectivization.map_comp second.toLinearMap second.injective
      first.toLinearMap first.injective) point

theorem projective_linear_action_mk
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (vector : VectorType) (nonzero : vector ≠ 0) :
    projectiveLinearAction automorphism (Projectivization.mk FieldType vector nonzero) =
      Projectivization.mk FieldType (automorphism vector)
        (by simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using nonzero) :=
  Projectivization.map_mk automorphism.toLinearMap automorphism.injective vector nonzero

theorem projective_linear_fixed_iff_eigenvector
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (vector : VectorType) (nonzero : vector ≠ 0) :
    projectiveLinearAction automorphism (Projectivization.mk FieldType vector nonzero) =
      Projectivization.mk FieldType vector nonzero ↔
      ∃ scalar : FieldType, automorphism vector = scalar • vector := by
  rw [projective_linear_action_mk, Projectivization.mk_eq_mk_iff']
  exact exists_congr (fun scalar : FieldType =>
    (eq_comm : scalar • vector = automorphism vector ↔ automorphism vector = scalar • vector))


end CFSG.SignalizerFunctor.Helpers
