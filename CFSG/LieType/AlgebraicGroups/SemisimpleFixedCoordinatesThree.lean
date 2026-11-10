module

public import CFSG.LieType.AlgebraicGroups.FixedPermutationTorus
public import CFSG.LieType.AlgebraicGroups.PermutationTorusAutomorphism
public import CFSG.LieType.AlgebraicGroups.FixedUnipotentConnected
public import CFSG.LieType.AlgebraicGroups.FixedCoordinateEmbedding
public import CFSG.LieType.AlgebraicGroups.FixedBruhatFactorization
public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple
public import CFSG.LieType.AlgebraicGroups.FixedComponentSmooth
import CFSG.Mathlib.RingTheory.ConnectedRegular

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

abbrev RationalGroup (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :=
  WithConv (H.obj →ₐ[k] k)

abbrev WeightTorus (k : Type u) [Field k] (r : ℕ) :=
  TauCeti.FiniteTypeCommHopfAlgCat.of k
    (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))

abbrev coordinateImage {H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (f : H →ₐc[k] K) : Subgroup (RationalGroup H) :=
  (TauCeti.AlgHom.mapDomain (A := k) f).range


structure StableTriangularCoordinates
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : H →ₐc[k] H) where
  rank : ℕ
  torusMap : H →ₐc[k] WeightTorus k rank
  torusSurjective : Function.Surjective torusMap
  torusMaximal : TauCeti.HopfIdeal.IsMaximalTorus k H.obj
    (TauCeti.HopfIdeal.kerOfSurjective torusMap torusSurjective)
  torusAut : WeightTorus k rank →ₐc[k] WeightTorus k rank
  torusEquivariant : torusMap.comp σ = torusAut.comp torusMap
  weightPerm : Equiv.Perm (ULift.{u} (Fin rank))
  torusOnWeight : ∀ i : ULift.{u} (Fin rank),
    torusAut (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
      MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (weightPerm i) 1)) 1
  positive : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k
  negative : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k
  positiveMap : H.obj ⟶ positive.obj
  negativeMap : H.obj ⟶ negative.obj
  positiveSurjective : Function.Surjective positiveMap.hom
  negativeSurjective : Function.Surjective negativeMap.hom
  positiveSmooth : Algebra.Smooth k positive
  negativeSmooth : Algebra.Smooth k negative
  positiveConnected : TauCeti.geometricallyConnectedCommHopfAlgProperty k positive.obj
  negativeConnected : TauCeti.geometricallyConnectedCommHopfAlgProperty k negative.obj
  positiveUnipotentPoints : ∀ x : RationalGroup positive, TauCeti.HopfAlgebra.IsUnipotentPoint x
  negativeUnipotentPoints : ∀ x : RationalGroup negative, TauCeti.HopfAlgebra.IsUnipotentPoint x
  positiveAut : positive →ₐc[k] positive
  negativeAut : negative →ₐc[k] negative
  positiveEquivariant : positiveMap.hom.comp σ = positiveAut.comp positiveMap.hom
  negativeEquivariant : negativeMap.hom.comp σ = negativeAut.comp negativeMap.hom
  positiveBorel : TauCeti.HopfIdeal k H
  negativeBorel : TauCeti.HopfIdeal k H
  isPositiveBorel : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H positiveBorel
  isNegativeBorel : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H negativeBorel
  positiveBorelPoints : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj positiveBorel
      (CommAlgCat.of k k) =
    coordinateImage torusMap ⊔
      coordinateImage positiveMap.hom
  negativeBorelPoints : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj negativeBorel
      (CommAlgCat.of k k) =
    coordinateImage torusMap ⊔
      coordinateImage negativeMap.hom
  torusNormalizesPositive : coordinateImage torusMap ≤
    Subgroup.normalizer (coordinateImage positiveMap.hom : Set (RationalGroup H))
  torusNormalizesNegative : coordinateImage torusMap ≤
    Subgroup.normalizer (coordinateImage negativeMap.hom : Set (RationalGroup H))
  opposite : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj positiveBorel
      (CommAlgCat.of k k) ⊓ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj negativeBorel
      (CommAlgCat.of k k) = coordinateImage torusMap
  inversion : RationalGroup H → Set (RationalGroup H)
  inversionPositive : ∀ n, inversion n ⊆ (coordinateImage positiveMap.hom : Set (RationalGroup H))
  inversionStable : ∀ n ∈ Subgroup.normalizer
      (coordinateImage torusMap : Set (RationalGroup H)),
    ∀ v ∈ inversion n, TauCeti.AlgHom.mapDomain σ v ∈
      inversion (TauCeti.AlgHom.mapDomain σ n)
  bruhatCover : ∀ g : RationalGroup H,
    ∃ u ∈ coordinateImage positiveMap.hom,
    ∃ n ∈ Subgroup.normalizer
      (coordinateImage torusMap : Set (RationalGroup H)),
    ∃ v ∈ inversion n, g = u * n * v
  bruhatUnique : ∀ u ∈ coordinateImage positiveMap.hom,
    ∀ n ∈ Subgroup.normalizer
      (coordinateImage torusMap : Set (RationalGroup H)),
    ∀ v ∈ inversion n,
    ∀ u' ∈ coordinateImage positiveMap.hom,
    ∀ n' ∈ Subgroup.normalizer
      (coordinateImage torusMap : Set (RationalGroup H)),
    ∀ v' ∈ inversion n', u * n * v = u' * n' * v' → u = u' ∧ n = n' ∧ v = v'

namespace StableTriangularCoordinates

variable {H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {σ : H →ₐc[k] H}
variable (D : StableTriangularCoordinates H σ)

abbrev torus : Subgroup (RationalGroup H) :=
  coordinateImage D.torusMap


abbrev normalizer : Subgroup (RationalGroup H) := Subgroup.normalizer (D.torus : Set _)

abbrev fixed (_D : StableTriangularCoordinates H σ) : Subgroup (RationalGroup H) :=
  TauCeti.fixedSubgroup (TauCeti.AlgHom.mapDomain σ)


end StableTriangularCoordinates

end CFSG.LieType.AlgebraicGroups
