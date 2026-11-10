/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FiniteFlat
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Generic freeness and faithful flatness of dominant affine group morphisms

This file is adapted from the TauCeti repository at `main` commit
`3bed7e37f3c504a99e8c07e9f309540812a7aa90`. It ports the generic-freeness development and
the dominance-to-faithful-flatness theorem added after the current CFSG dependency pin
`6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380`. The declarations are reproduced in the
`CFSG.ThirdParty.TauCeti` namespace with unchanged statements, so that a later TauCeti bump
does not clash with the upstream names.

The source files and their main declarations are:

* `TauCeti/LinearAlgebra/FreeModule/Filtration.lean`:
  `CFSG.ThirdParty.TauCeti.Module.Free.of_filtration`, a module with an exhaustive filtration
  by free subquotients is free;
* `TauCeti/RingTheory/Spectrum/Prime/FreeLocus.lean`:
  `CFSG.ThirdParty.TauCeti.Module.mem_freeLocus_of_mem_minimalPrimes` and
  `CFSG.ThirdParty.TauCeti.Module.iInter_freeLocus_subquotient_subset_freeLocus`; the upstream
  `Module.freeLocus_nonempty` and `PrimeSpectrum.flat_localization_of_comap_mem_freeLocus`
  already exist at the pin and are not redeclared (only the latter is used here);
* `TauCeti/RingTheory/Spectrum/Prime/Topology.lean`:
  `CFSG.ThirdParty.TauCeti.PrimeSpectrum.dense_of_forall_mem_minimalPrimes`;
* `TauCeti/RingTheory/Spectrum/Prime/GenericFreeness.lean`:
  `CFSG.ThirdParty.TauCeti.Module.freeLocus_mem_nhds_polynomial` and
  `CFSG.ThirdParty.TauCeti.Module.freeLocus_mem_nhds_of_surjective` (private upstream, made
  public here), and the main declarations
  `CFSG.ThirdParty.TauCeti.Module.freeLocus_mem_nhds_of_mem_minimalPrimes` and
  `CFSG.ThirdParty.TauCeti.Module.dense_interior_freeLocus_of_finiteType`;
* `TauCeti/Algebra/AlgebraicGroup/CommHopfAlgCat/Flat.lean`:
  `CFSG.ThirdParty.TauCeti.CommHopfAlgCat.faithfullyFlat_of_dominant`.

The statements are unchanged. The proofs are ported verbatim except for the following
adaptations to the pinned API:

* every ported declaration is placed in a namespace rooted at `CFSG.ThirdParty.TauCeti`, and
  references to ported declarations are correspondingly qualified, namely
  `CFSG.ThirdParty.TauCeti.Module.Free.of_filtration`,
  `CFSG.ThirdParty.TauCeti.PrimeSpectrum.dense_of_forall_mem_minimalPrimes` and
  `CFSG.ThirdParty.TauCeti.Module.dense_interior_freeLocus_of_finiteType`;
* the pinned TauCeti modules `TauCeti.RingTheory.Spectrum.Prime.FreeLocus`,
  `TauCeti.RingTheory.Spectrum.Prime.Topology` and
  `TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FiniteFlat` are imported in place of the
  3bed ones, and the pinned declarations
  `PrimeSpectrum.flat_localization_of_comap_mem_freeLocus`,
  `TauCeti.CommHopfAlgCat.flat_localization_kernel_iff`,
  `TauCeti.CommHopfAlgCat.flat_iff_flat_localization_augmentation`,
  `TauCeti.CommHopfAlgCat.faithfullyFlat_iff_flat_of_injective` and
  `TauCeti.denseRange_kernelPoint` are reused;
* the TauCeti-specific point construction `AlgHom.kernelPoint` (and
  `AlgHom.kernelPoint_asIdeal`) is written `TauCeti.AlgHom.kernelPoint` (respectively
  `TauCeti.AlgHom.kernelPoint_asIdeal`), since it lives in the pinned TauCeti namespace and
  not in the ported one;
* the two private upstream lemmas are made public with docstrings.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 24.1.
* The Stacks Project, Tag 051R (and Tag 051Z), for generic freeness.
* J. S. Milne, *Algebraic Groups* (2017), §5 and Propositions 1.65(a) and 1.70.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14, for faithful flatness of
  dominant homomorphisms via generic flatness and translation.
-/

public section

open Module
open DirectSum
open Polynomial Topology
open PrimeSpectrum
open CategoryTheory WithConv

namespace CFSG.ThirdParty.TauCeti

namespace Module.Free

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]


end Module.Free

namespace Module

section Reduced

variable {R : Type*} (M : Type*) [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M]


end Reduced

section Filtration

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]


end Filtration

end Module

namespace PrimeSpectrum

variable {R : Type*} [CommSemiring R]


end PrimeSpectrum

namespace Module

universe uA uR uM

variable {A : Type uA} [CommRing A]


end Module

attribute [local instance] RingHom.ker_isPrime

namespace CommHopfAlgCat

universe u v


end CommHopfAlgCat

end CFSG.ThirdParty.TauCeti
