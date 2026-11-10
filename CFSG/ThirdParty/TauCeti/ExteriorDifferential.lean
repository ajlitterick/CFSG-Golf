/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors; CFSG contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic.Abel

/-!
# The differential of an exterior algebra comodule

The SAME native comodule differential acts on the exterior algebra by the ordinary product
rule and sends `ι(m)` to `ι(d(m))`. These identities supply the infinitesimal determinant-line
bridge in Chevalley's theorem, without a factorial or a characteristic restriction.

The tensor-contraction multiplication argument generalizes the private `tensorComponent_mul`
in `TauCeti/Algebra/AlgebraicGroup/Tangent/InvariantDerivation.lean` at commit
`6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380`. That source is copyright (c) 2026 The Tau Ceti
contributors and distributed under Apache 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Here the left tensor factor is an arbitrary, possibly noncommutative algebra, which is needed
for the exterior algebra. The existing native coaction, differential and generator inclusion
are reused; no second Lie action is defined. Names are kept in the `CFSG.ThirdParty` namespace.

## References

* A. Borel, *Linear Algebraic Groups*, second edition (1991), Theorem 5.1.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
-/

public noncomputable section

open scoped TensorProduct
open LinearMap TauCeti

universe u v w

variable {k : Type u} [CommRing k] {H : Type v} [CommRing H] [_root_.Bialgebra k H]

namespace CFSG.ThirdParty.TauCeti


namespace Comodule

open _root_.TauCeti.Comodule

variable {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]


attribute [local instance] exteriorAlgebra


end Comodule

end CFSG.ThirdParty.TauCeti
