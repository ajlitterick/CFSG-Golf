module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
public import TauCeti.RingTheory.FiniteType.FiniteRange
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Data.EReal.Operations
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Sheaves.Init
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint

public noncomputable section

open WithConv
open scoped TensorProduct
open TauCeti

namespace CFSG.LieType.AlgebraicGroups.ReductiveDescent

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem pow_finrank_eq_zero_of_isNilpotent {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {f : Module.End K V} (hf : IsNilpotent f) :
    f ^ Module.finrank K V = 0 := by
  have : Module.Free K V := Module.Free.of_divisionRing K V
  have hchar : LinearMap.charpoly f = Polynomial.X ^ Module.finrank K V :=
    (LinearMap.isNilpotent_iff_charpoly f).mp hf
  have h := LinearMap.aeval_self_charpoly f
  rw [hchar, map_pow, Polynomial.aeval_X] at h
  exact h

theorem pow_prime_pow_eq_one_of_sub_one_pow_eq_zero {R : Type*} [Ring R] {p E d : ℕ}
    [Fact p.Prime] [CharP R p] {f : R} (h : (f - 1) ^ d = 0) (hd : d ≤ p ^ E) :
    f ^ (p ^ E) = 1 := by
  have hf : f = (f - 1) + 1 := (sub_add_cancel f 1).symm
  rw [hf, add_pow_char_pow_of_commute p E (Commute.one_right _), one_pow]
  have hzero : (f - 1) ^ p ^ E = 0 := by
    rw [show p ^ E = d + (p ^ E - d) from (Nat.add_sub_cancel' hd).symm, pow_add, h, zero_mul]
  rw [hzero, zero_add]

theorem mk_one_tmul_basePointsRepresentation {K H M : Type*} [Field K] [CommRing H]
    [_root_.HopfAlgebra K H] [AddCommMonoid M] [Module K M] [Comodule K H M]
    (g : WithConv (H →ₐ[K] K)) (m : M) :
    ((TensorProduct.mk K K M) (1 : K)) (Comodule.basePointsRepresentation (H := H) M g m) =
      Comodule.endOfPoint M g.ofConv (((TensorProduct.mk K K M) (1 : K)) m) := by
  rw [TensorProduct.mk_apply, TensorProduct.mk_apply, Comodule.endOfPoint_tmul, one_smul,
    Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]

theorem mk_one_tmul_injective {K M : Type*} [CommSemiring K] [AddCommMonoid M] [Module K M] :
    Function.Injective ((TensorProduct.mk K K M) (1 : K)) := by
  intro a b hab
  have := congrArg (TensorProduct.lid K M) hab
  simpa [TensorProduct.mk_apply, TensorProduct.lid_tmul] using this

theorem endOfPoint_pow {K H M : Type*} [CommSemiring K] [Semiring H] [Bialgebra K H]
    [AddCommMonoid M] [Module K M] [Comodule K H M] {A : Type*} [CommSemiring A] [Algebra K A]
    (g : WithConv (H →ₐ[K] A)) (n : ℕ) :
    Comodule.endOfPoint M ((g ^ n).ofConv) = Comodule.endOfPoint M g.ofConv ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero,
        Comodule.endOfPoint_convOne (R := K) (H := H) (V := M) (A := A)]
      apply LinearMap.ext
      intro x
      rw [Module.End.one_apply]
      rfl
  | succ n ih =>
      rw [show g ^ (n + 1) = g ^ n * g from pow_succ g n]
      rw [Comodule.endOfPoint_convMul (R := K) (H := H) (V := M) (A := A)]
      rw [ih]
      apply LinearMap.ext
      intro x
      rfl

theorem endOfPoint_pow_prime_pow_eq_one {K H M : Type*} [Field K] [CommRing H]
    [_root_.HopfAlgebra K H] [AddCommMonoid M] [Module K M] [Comodule K H M]
    [Module.Finite K M] {p : ℕ} [CharP K p] (hp : p.Prime) (E : ℕ)
    (hE : Module.finrank K (K ⊗[K] M) ≤ p ^ E) (g : WithConv (H →ₐ[K] K))
    (hunip : IsNilpotent (Comodule.endOfPoint M g.ofConv - 1)) :
    Comodule.endOfPoint M g.ofConv ^ (p ^ E) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have : Module.Finite K (K ⊗[K] M) := Module.Finite.equiv (TensorProduct.lid K M).symm
  have hpow : (Comodule.endOfPoint M g.ofConv - 1) ^ Module.finrank K (K ⊗[K] M) = 0 :=
    pow_finrank_eq_zero_of_isNilpotent hunip
  rcases subsingleton_or_nontrivial (K ⊗[K] M) with hW | hW
  · have := hW
    have : Subsingleton (Module.End K (K ⊗[K] M)) :=
      ⟨fun a b => LinearMap.ext fun m => Subsingleton.elim _ _⟩
    exact Subsingleton.elim _ _
  · have : FaithfulSMul K (Module.End K (K ⊗[K] M)) := inferInstance
    have : CharP (Module.End K (K ⊗[K] M)) p :=
      charP_of_injective_algebraMap' (A := Module.End K (K ⊗[K] M)) K p
    exact pow_prime_pow_eq_one_of_sub_one_pow_eq_zero (R := Module.End K (K ⊗[K] M))
      (f := Comodule.endOfPoint M g.ofConv) (p := p) (E := E)
      (d := Module.finrank K (K ⊗[K] M)) hpow hE


end CFSG.LieType.AlgebraicGroups.ReductiveDescent
