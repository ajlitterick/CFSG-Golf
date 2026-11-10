module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Nakayama

public noncomputable section

namespace CFSG

open MvPolynomial

universe u v w

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A] {σ : Type w}

attribute [local instance] MvPolynomial.gradedAlgebra


end CFSG
