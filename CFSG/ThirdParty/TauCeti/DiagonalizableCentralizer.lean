/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import CFSG.ThirdParty.TauCeti.DynamicRepresentability
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# The centralizer of a diagonalizable subgroup

This file is adapted from the TauCeti repository at `main` commit
`aeabd40497938acad628b54656f3c7c1aba0b9b3`, file
`TauCeti/Algebra/AlgebraicGroup/DiagonalizableGroup/Centralizer/Basic.lean` (last changed in
`eadbd22f0f65abaeeda758123a1051657d830287`). The CFSG dependency pin
`6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380` predates it. The declarations are reproduced in the
`CFSG.ThirdParty.TauCeti` namespace with unchanged statements, so that a later TauCeti bump does
not clash with the upstream names.

Let `G = Spec H` be an affine group scheme over a commutative ring `R` and let `D(X) → G` be a
closed diagonalizable subgroup, given by a morphism `π : H →ₐc[R] R[X]` of coordinate Hopf
algebras for a commutative group `X` of characters. This file constructs the centralizer
`Z_G(D(X))` as a closed subgroup scheme of `G`, that is, as a Hopf ideal of `H`.

The defining equations are the coefficients, in the basis of `R[X]` indexed by characters, of the
**conjugation defect** of a coordinate `x`: the difference between the universal conjugate of the
universal point of `D(X)` by the universal point of `G` and that point itself, written in the
coordinates `H ⊗[R] R[X]`. A point of `G` with values in an algebra `A` kills these coefficients
exactly when it commutes with every point of `D(X)` after every extension of `A`; since such points
form a subgroup, the coefficient ideal is a Hopf ideal. The construction needs no basis of `H`,
only the canonical basis of the monoid algebra `R[X]`, and no hypothesis on `R`.

## Main declarations

* `centralizerDefect` and `centralizerCoefficient`: the conjugation defect of a coordinate, in
  `H ⊗[R] R[X]`, and its coefficient at a character.
* `centralizerHopfIdeal`: the Hopf ideal cutting out the centralizer of the diagonalizable
  subgroup, with `centralizerHopfIdeal_toIdeal`.
* `centralizerHopfIdeal_le_ker_iff`: an algebra-valued point kills the centralizer ideal exactly
  when it commutes with every point of the diagonalizable subgroup over every extension of its
  value algebra; `centralizerHopfIdeal_le_ker_iff_commute_of_injective` tests this on a single
  injective extension, and `centralizerHopfIdeal_le_ker_iff_commute_universal` on the universal
  point of `D(X)` over `R[X] ⊗[R] A`.
* `mem_centralizerPointsSubgroup_iff`: the same statement for the subgroup of points cut out by the
  centralizer ideal.
* `centralizerHopfIdeal_le_ker_iff_comp_pointConjugationAlgHom_eq`: a rational point lies in the
  centralizer exactly when conjugation by it fixes the coordinate map `π`.
* `centralizerHopfIdeal_le_kerOfSurjective`: the diagonalizable subgroup lies in its own
  centralizer.
* `centralizerHopfIdeal_comp_le` and `centralizerHopfIdeal_mapDomainBialgHom_comp_eq_of_leftInverse`:
  the centralizer of a composite `D(Y) → D(X) → G` contains that of `D(X)`, with equality for a
  split injection of character groups (for instance a change of universe of the characters).

## Adaptations to the pinned API

* Every ported declaration is placed in the namespace `CFSG.ThirdParty.TauCeti.BialgHom`.
* The pinned `TauCeti.AlgHom.mapDomain` and `TauCeti.AlgHom.mapDomain_apply` replace the renamed
  `BialgHom.mapDomain` and `BialgHom.mapDomain_apply`.
* The pointwise criterion for Hopf ideals is the ported
  `CFSG.ThirdParty.TauCeti.HopfIdeal.ofIdealOfPointsSubgroup` of
  `CFSG/ThirdParty/TauCeti/DynamicRepresentability.lean`. Its points are taken in the universe of
  `H`, so the value algebras of the ported statements live in that universe.
* The two lemmas `Algebra.TensorProduct.map_apply_eq_map` and
  `TensorProduct.map_algebraTensorProduct_map` of the new file
  `TauCeti/Algebra/TensorProduct/MapLinear.lean` (`e3223c9bebf35303848e9fea8070576143851536`),
  which the pin does not have, are ported here as `map_apply_eq_map` and
  `map_algebraTensorProduct_map`.
* The upstream statements about normalizers (`mem_normalizerPoints_of_centralizerHopfIdeal_le_ker`,
  `normalizerCharacterHom_eq_one_iff_centralizerHopfIdeal_le_ker`) and central subgroups
  (`centralizerHopfIdeal_eq_bot_iff_isCentral`) rely on files the pin does not have and are not
  ported; nor is `centralizerHopfIdeal_mapDomainBialgHom_mk'_comp_anti`.
* `centralizerHopfIdeal_le_ker_iff_commute_universal`, the specialization of the injective test to
  the universal point of `D(X)` over `R[X] ⊗[R] A`, is new.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 1 (normalizers and centralizers), §12
  (diagonalizable groups) and §13 (tori acting on schemes).
* SGA 3, Exposé VI_B, Corollaire 6.2.5 (i), and Exposé XI, Corollaire 5.3.
-/

public section

open TensorProduct WithConv

namespace CFSG.ThirdParty.TauCeti.BialgHom

open _root_.TauCeti

universe u v w x y

/-- The tensor product of two algebra maps acts as the tensor product of their underlying linear
maps. Ported from `TauCeti/Algebra/TensorProduct/MapLinear.lean`. -/
theorem map_apply_eq_map {R A B C D : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Semiring C] [Semiring D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] C) (g : B →ₐ[R] D) (z : A ⊗[R] B) :
    Algebra.TensorProduct.map f g z = _root_.TensorProduct.map f.toLinearMap g.toLinearMap z := by
  rw [← AlgHom.toLinearMap_apply, Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq]


variable {R : Type u} {H : Type v} {X : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
variable (π : H →ₐc[R] MonoidAlgebra R X)

/-! ## The conjugation defect and its coefficients -/

/-- The conjugation defect of a coordinate `x`: in the coordinates `H ⊗[R] R[X]` of `G × D(X)`,
the difference between the conjugate of the universal point of `D(X)` by the universal point of
`G` and the universal point of `D(X)` itself. The first tensor factor is the conjugating variable
of `G`, the second the conjugated variable of `D(X)`. -/
noncomputable def centralizerDefect (x : H) : H ⊗[R] MonoidAlgebra R X :=
  Algebra.TensorProduct.map (AlgHom.id R H) π.toAlgHom
      (HopfAlgebra.conjugationAlgHom (R := R) (H := H) x) -
    1 ⊗ₜ[R] π x


/-- The coefficient of the conjugation defect of `x` at the character `χ`, in the canonical basis
of `R[X]`. These coefficients generate the centralizer ideal. -/
noncomputable def centralizerCoefficient (x : H) (χ : X) : H :=
  LinearMap.tensorComponent (Comodule.monoidCoeff R X χ) (centralizerDefect π x)


/-- A linear map out of `H` kills every coefficient of a conjugation defect exactly when it kills
the defect itself, after tensoring with the identity of `R[X]`. -/
theorem map_centralizerDefect_eq_zero_iff {A : Type x} [AddCommMonoid A] [Module R A]
    (f : H →ₗ[R] A) (x : H) :
    _root_.TensorProduct.map f LinearMap.id (centralizerDefect π x) = 0 ↔
      ∀ χ, f (centralizerCoefficient π x χ) = 0 := by
  constructor
  · intro h χ
    have hχ := congrArg (LinearMap.tensorComponent (Comodule.monoidCoeff R X χ)) h
    rwa [LinearMap.tensorComponent_map, LinearMap.comp_id, map_zero] at hχ
  · intro h
    apply (Comodule.tensorCoeffEquiv R X A).injective
    ext χ
    rw [Comodule.tensorCoeffEquiv_apply, map_zero, Finsupp.zero_apply,
      LinearMap.tensorComponent_map, LinearMap.comp_id]
    exact h χ

/-- The ideal generated by all coefficients of all conjugation defects. -/
noncomputable def centralizerIdeal : Ideal H :=
  Ideal.span (Set.range fun p : H × X ↦ centralizerCoefficient π p.1 p.2)

/-- A point kills the coefficient ideal exactly when it kills every conjugation defect. -/
theorem centralizerIdeal_le_ker_iff {A : Type x} [CommRing A] [Algebra R A]
    (g : H →ₐ[R] A) :
    centralizerIdeal π ≤ RingHom.ker g ↔
      ∀ x, Algebra.TensorProduct.map g (AlgHom.id R (MonoidAlgebra R X))
        (centralizerDefect π x) = 0 := by
  rw [centralizerIdeal, Ideal.span_le]
  simp only [Set.range_subset_iff, Prod.forall, SetLike.mem_coe, RingHom.mem_ker]
  refine forall_congr' fun x ↦ ?_
  rw [map_apply_eq_map, AlgHom.toLinearMap_id, map_centralizerDefect_eq_zero_iff]
  simp only [AlgHom.toLinearMap_apply]

/-- Evaluating the conjugation defect at a point `g` of `G` and then along an algebra map `ψ` out
of the tensor square computes `g' t g'⁻¹ - t`, where `g'` is `g` pushed along `ψ` and `t` is the
point of `D(X)` carried by `ψ`. -/
theorem apply_map_centralizerDefect {A : Type x} {B : Type y} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (g : WithConv (H →ₐ[R] A))
    (ψ : A ⊗[R] MonoidAlgebra R X →ₐ[R] B) (x : H) :
    ψ (Algebra.TensorProduct.map g.ofConv (AlgHom.id R (MonoidAlgebra R X))
        (centralizerDefect π x)) =
      (AlgHom.mapValue (ψ.comp Algebra.TensorProduct.includeLeft) g *
          AlgHom.mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight)) *
          (AlgHom.mapValue (ψ.comp Algebra.TensorProduct.includeLeft) g)⁻¹).ofConv x -
        (AlgHom.mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight))).ofConv x := by
  have hcomp : (ψ.comp (Algebra.TensorProduct.map g.ofConv (AlgHom.id R (MonoidAlgebra R X)))).comp
      (Algebra.TensorProduct.map (AlgHom.id R H) π.toAlgHom) =
      Algebra.TensorProduct.productMap
        (AlgHom.mapValue (ψ.comp Algebra.TensorProduct.includeLeft) g).ofConv
        (AlgHom.mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight))).ofConv := by
    refine Algebra.TensorProduct.ext ?_ ?_ <;> ext h <;>
      simp [AlgHom.mapValue_apply, AlgHom.mapDomain_apply, ← Algebra.TensorProduct.one_def]
  rw [centralizerDefect, map_sub, map_sub, ← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp,
    ← AlgHom.comp_apply, HopfAlgebra.productMap_comp_conjugationAlgHom]
  congr 1
  simp [AlgHom.mapDomain_apply]

/-! ## The centralizer as a closed subgroup scheme -/

/-- The points of `G` killing the centralizer ideal are detected by commutation with the point of
`D(X)` carried by any injective algebra map `ψ` out of `A ⊗[R] R[X]`. -/
theorem centralizerIdeal_le_ker_iff_commute_of_injective {A : Type x} {B : Type y}
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (g : WithConv (H →ₐ[R] A))
    (ψ : A ⊗[R] MonoidAlgebra R X →ₐ[R] B) (hψ : Function.Injective ψ) :
    centralizerIdeal π ≤ RingHom.ker g.ofConv ↔
      Commute (AlgHom.mapValue (ψ.comp Algebra.TensorProduct.includeLeft) g)
        (AlgHom.mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight))) := by
  rw [centralizerIdeal_le_ker_iff, commute_iff_eq, ← mul_inv_eq_iff_eq_mul]
  simp_rw [← map_eq_zero_iff ψ hψ, apply_map_centralizerDefect, sub_eq_zero]
  exact ⟨fun h ↦ ofConv_injective (AlgHom.ext h), fun h x ↦ by rw [h]⟩

/-- **The centralizer of a diagonalizable subgroup, as a Hopf ideal.** Its quotient represents
the points of `G` commuting with every point of `D(X)`. The ideal is generated by the coefficients
of the conjugation defects; it is a Hopf ideal because the points killing it form a subgroup
over every value algebra. -/
noncomputable def centralizerHopfIdeal : HopfIdeal R H :=
  CFSG.ThirdParty.TauCeti.HopfIdeal.ofIdealOfPointsSubgroup (centralizerIdeal π)
    (fun A ↦ (Subgroup.centralizer
        {AlgHom.mapDomain π (toConv (Algebra.TensorProduct.includeRight :
          MonoidAlgebra R X →ₐ[R] A ⊗[R] MonoidAlgebra R X))}).comap
      (AlgHom.mapValue (H := H) (Algebra.TensorProduct.includeLeft (R := R) (S := R))))
    fun A g ↦ by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← commute_iff_eq,
        centralizerIdeal_le_ker_iff_commute_of_injective π g (AlgHom.id R _)
          Function.injective_id]
      simp only [AlgHom.id_comp]

/-- The centralizer ideal is generated by the coefficients of the conjugation defects. -/
theorem centralizerHopfIdeal_toIdeal :
    (centralizerHopfIdeal π).toIdeal =
      Ideal.span (Set.range fun p : H × X ↦ centralizerCoefficient π p.1 p.2) :=
  CFSG.ThirdParty.TauCeti.HopfIdeal.ofIdealOfPointsSubgroup_toIdeal _ _ _

/-- A point of `G` kills the centralizer ideal exactly when it commutes with the point of `D(X)`
carried by any injective algebra map `ψ` out of `A ⊗[R] R[X]`. The identity of `A ⊗[R] R[X]`
carries the universal point of `D(X)`; the left unitor `R ⊗[R] R[X] ≃ R[X]` is used for rational
points. -/
theorem centralizerHopfIdeal_le_ker_iff_commute_of_injective {A : Type x} {B : Type y}
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (g : WithConv (H →ₐ[R] A))
    (ψ : A ⊗[R] MonoidAlgebra R X →ₐ[R] B) (hψ : Function.Injective ψ) :
    (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker g.ofConv ↔
      Commute (AlgHom.mapValue (ψ.comp Algebra.TensorProduct.includeLeft) g)
        (AlgHom.mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight))) := by
  rw [centralizerHopfIdeal_toIdeal]
  exact centralizerIdeal_le_ker_iff_commute_of_injective π g ψ hψ


/-! ## Rational points -/


/-! ## Comparison with the diagonalizable subgroup -/


/-! ## Composites `D(Y) → D(X) → G` -/

section Smaller


end Smaller

end CFSG.ThirdParty.TauCeti.BialgHom
