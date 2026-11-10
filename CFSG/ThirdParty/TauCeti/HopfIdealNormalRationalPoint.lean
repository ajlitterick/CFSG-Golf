/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.RingTheory.FiniteType.PointSeparation
public import TauCeti.RingTheory.FiniteType.Tensor.Product
public import Mathlib.RingTheory.FiniteStability
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Normality of reduced closed subgroups from rational points

This file is adapted from the TauCeti repository:

* `TauCeti/Algebra/AlgebraicGroup/HopfIdeal/Normal/RationalPoint.lean`, at TauCeti `main`
  commit `f3825ea4a4d2c7b7030c4a885dca8785b4bc73a0`, which contains
  `isNormal_of_forall_le_conjugate`, `isNormal_iff_forall_le_conjugate` and
  `IsNormal.comapOfSurjective_of_forall_iso`;
* `TauCeti/Algebra/AlgebraicGroup/HopfIdeal/Conjugation.lean`, at TauCeti `main`
  commit `3edb527dbf3007ec567f305c5543c669ba9a1988`, which contains
  `IsNormal.le_conjugate`.

Copyright (c) 2026 The Tau Ceti contributors; released under the Apache 2.0 license
(https://www.apache.org/licenses/LICENSE-2.0).

The current CFSG dependency pin (`6e0c6acab`) predates these declarations. They are reproduced
in the `CFSG.ThirdParty.TauCeti` namespace so that a later TauCeti bump does not clash with the
upstream names. The statements are unchanged. The proofs are ported verbatim except for the
following adaptations to the pinned API:

* `Ideal.rightTensorIdeal (R := R) (A := H)` is written
  `TauCeti.HopfIdeal.rightTensorIdeal (R := R) (H := H)`, and similarly for
  `rightTensorIdeal_le_iff` and `ker_tensorProduct_map_id_quotient`;
* `TauCeti.HopfIdeal.conjugate_eq_comapOfSurjective` replaces unfolding the `conjugate`
  definition, which is not exposed at the pin;
* the three declarations are placed in namespaces rooted at `CFSG.ThirdParty.TauCeti`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.d and §3.5.
-/

public section

open WithConv
open scoped TensorProduct
open CategoryTheory

namespace CFSG.ThirdParty.TauCeti

universe u

namespace HopfIdeal


end HopfIdeal

end CFSG.ThirdParty.TauCeti
