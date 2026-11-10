/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import CFSG.ThirdParty.TauCeti.DiagonalizableCentralizer
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace
import TauCeti.Algebra.DualNumber.Convolution

/-!
# The Lie algebra of the centralizer of a diagonalizable subgroup

This file is adapted from the TauCeti repository, file
`TauCeti/Algebra/AlgebraicGroup/DiagonalizableGroup/Centralizer/Tangent.lean` as of commit
`3c85a89bedd31a6470cac38648f51cc8310b173d` (the file is unchanged at `main` commit
`9b5ddaa11d617c84d46732ef8318190eb32842c6`), released under the Apache 2.0 license. The CFSG
dependency pin `6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380` predates it. It builds on the port of
`Centralizer/Basic.lean` in `CFSG/ThirdParty/TauCeti/DiagonalizableCentralizer.lean`, and its
declarations are placed in the same namespace `CFSG.ThirdParty.TauCeti.BialgHom`.

Let `G = Spec H` be an affine group scheme over a commutative ring `R` and `D(X) → G` a closed
diagonalizable subgroup with coordinate map `π : H →ₐc[R] R[X]`. The centralizer `Z_G(D(X))` is
the closed subgroup scheme cut out by `centralizerHopfIdeal π`. This file identifies its Lie
algebra inside the Lie algebra of `G`: it is the subspace fixed by the adjoint action of `D(X)`,
that is, the weight space of the trivial character in the weight decomposition of `Lie G` under
`D(X)`.

Both sides are conditions on a tangent vector `d` at the identity of `G`, viewed as a counit-valued
derivation of `H`. The tangent vector lies in the Lie algebra of the centralizer when it kills the
coefficients of the conjugation defects; evaluating a derivation on the conjugation defect is
differentiating the conjugating variable, and this yields the convolution commutator of `d` with
the universal point of `D(X)`. The adjoint action of the universal point of `D(X)` on `d`, which
differentiates the conjugated variable, is the convolution conjugate `π ⋆ d ⋆ π⁻¹`. Both
conditions therefore say that `d` and `π` commute in the convolution algebra. The convolution
commutator is computed on dual-number points, as the infinitesimal coefficient of the conjugate of
`π` by the tangent point of `d`.

The hypotheses are those needed to speak of the adjoint representation on the single module
`Lie G = Module.Dual R (Bialgebra.CotangentSpace R H)`: the augmentation cotangent space of `H`
is finite projective. No smoothness, reducedness or field hypothesis enters.

## Main declarations

* `cotangentLinearEquiv_mem_lieSubalgebra_centralizerHopfIdeal_iff`: **a tangent vector lies in
  the Lie algebra of the centralizer of `D(X)` exactly when it has trivial weight under `D(X)`.**
* `lieSubalgebra_centralizerHopfIdeal_toSubmodule`: the Lie algebra of the centralizer is the
  trivial weight space, transported along cotangent duality.
* `mem_adjointWeightSpace_iff_adDerivation`: weight-space membership tested on the universal point
  of `D(X)`, for `R`, `H` and `X` in independent universes.

## Adaptations to the pinned API

* **Universes.** Upstream takes `R`, `H` and `X` in one universe, because its proof starts from
  `Derivation.mem_adjointWeightSpace_iff_universalPointAction`, whose universal point of `D(X)` is
  an object of `CommAlgCat` in the universe of `H`. Here `R : Type u`, `H : Type v` and
  `X : Type w` are independent, as in the port of `Centralizer/Basic.lean`. That criterion and
  `Derivation.tangentScalarExtensionEquiv_adjointAction` are replaced by the new
  `mem_adjointWeightSpace_iff_adDerivation`. Its proof pushes the pinned
  `Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint`, at the universal point of
  `G` over `ULift H`, forward to an arbitrary value algebra: the point action of a comodule
  (`TauCeti.Comodule.rTensor_comp_endOfPoint`), tangent scalar extension
  (`Derivation.mapValue_tangentScalarExtensionEquiv`) and the adjoint action
  (`Derivation.mapValue_adDerivation`) are natural in the value algebra. Accordingly the
  coefficient algebra `CommAlgCat.of R R[X]` of upstream is `R[X]` itself. The tori
  `D(Multiplicative (Fin r →₀ ℤ))` of `CFSG.LieType.AlgebraicGroups.TorusCentralizerScheme` need
  this: their character group lives in `Type`, their Hopf algebra in an arbitrary universe.
* `Derivation.tangentScalarExtensionEquiv_tmul` and `Bialgebra.CounitAlgebra.algEquivSelf_map`,
  which the pin does not have, are replaced by the private `tangentScalarExtensionEquiv_one_tmul`
  and by a direct computation in `algEquivSelf_mapValue_ofId_apply`.
* `TensorProduct.map_algebraTensorProduct_map` is the ported `map_algebraTensorProduct_map`.
* The section `Smaller` (the centralizer of `D(Y) → D(X) → G` for `q : X →* Y`) relies on
  `Derivation.adjointWeightSpace_mapDomainBialgHom_comp`, which the pin does not have, and is not
  ported.

## Conventions

The first tensor factor of `TauCeti.HopfAlgebra.conjugationAlgHom` is the conjugating variable: it
is `i₁ * i₂ * i₁⁻¹`, Milne's `Ad(g)(x) = g x g⁻¹`. The conjugation defect `centralizerDefect` keeps
`G` in that factor and puts `D(X)` in the conjugated one, and
`TauCeti.HopfAlgebra.pointConjugationAlgHom g` specializes the same first factor to a rational
point `g`. Lie-algebra membership differentiates the conjugating variable; the weight condition is
the adjoint action `Ad(π) d = π ⋆ d ⋆ π⁻¹` of the universal point of `D(X)`
(`Derivation.adDerivation`), which differentiates the conjugated variable.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a (the Lie algebra of a closed subgroup) and §13
  (tori acting on schemes).
* SGA 3, Exposé XI, Corollaire 5.3.
-/

public section

open TensorProduct TrivSqZeroExt WithConv

namespace CFSG.ThirdParty.TauCeti.BialgHom

open _root_.TauCeti

universe u v w x

variable {R : Type u} {H : Type v} {X : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]


section Universal

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

attribute [local instance] Derivation.adjointComodule


end Universal


end CFSG.ThirdParty.TauCeti.BialgHom
