/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import CFSG.LieType.AlgebraicGroups.CommutativeReductiveDiagonalizable
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Commuting
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
public import TauCeti.Algebra.Bialgebra.GroupLike.Torsion
public import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Vector
public import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization

/-!
# Semisimple points of connected commutative affine groups

The semisimple Jordan projection of a reduced commutative affine group is a regular
Hopf endomorphism. Its image is a torus when the group is connected, and contains the
original semisimple points. It is the unique maximal torus.

The construction of the regular endomorphism and its closed image is adapted from
TauCeti commit `c160684bdc6e37018f3010604f9c0837be53d574`, Apache-2.0, files
`Representation/JordanDecomposition/{Commutative,ClosedFactors,MaximalTorus}.lean`.
The weight calculation is replaced by the existing repository result
`CommutativeReductive.exists_groupLike_eval`, so no weight-space theory is duplicated.
At the CFSG pin, point precomposition uses `TauCeti.AlgHom.mapDomain`; image connectedness
uses the injective image factor, and torus recognition uses the existing torsion-free
character-group equivalence. The kernel/image construction and the original point are
unchanged mathematically.

The shared `RegularJordan` lemmas require actual coordinate regularity and multiplicativity
of the semisimple map. `CommutativeJordan` proves these in the commutative case, preserving
its original theorem types. `CentralJordan` proves them for a connected solvable group whose
semisimple parts are central; `NilpotentSemisimple` supplies that centrality unconditionally
for connected nilpotent groups. The generalized image proofs are shared rather than copied.

This is the commutative case used in the connected-solvable step of semisimple point
containment (Springer 6.3.5(i), then 6.4.5(ii)). It supplies the commutative branch of
native Borel maximal-torus conjugacy; general point containment remains separate.

## References

* T. A. Springer, *Linear Algebraic Groups*, 2nd ed. (1998), Theorem 3.1.1,
  Corollary 3.1.2 and Theorem 6.3.5(i).
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Theorem 4.7.
-/

public noncomputable section
open TauCeti WithConv
open scoped TensorProduct
open scoped commutatorElement
namespace CFSG.ThirdParty.TauCeti.CommutativeJordan
universe u


end CFSG.ThirdParty.TauCeti.CommutativeJordan

namespace CFSG.ThirdParty.TauCeti.CentralJordan
universe u


section CentralParts


end CentralParts

end CFSG.ThirdParty.TauCeti.CentralJordan

namespace CFSG.ThirdParty.TauCeti.RegularJordan
universe u


open CategoryTheory


end CFSG.ThirdParty.TauCeti.RegularJordan


namespace CFSG.ThirdParty.TauCeti.CommutativeJordan
universe u


end CFSG.ThirdParty.TauCeti.CommutativeJordan
