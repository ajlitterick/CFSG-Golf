module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Comultiplication
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
public import TauCeti.RingTheory.FiniteType.PointSeparation
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import CFSG.Mathlib.RingTheory.ConnectedRegular
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

public noncomputable section

open WithConv

namespace CFSG.LieType.AlgebraicGroups.TorusConjugacy

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

section Dense


theorem exists_forall_apply_eq_zero_of_forall_exists {Z : Type*} [CommRing Z] [Algebra k Z]
    [Algebra.FiniteType k Z] [IsDomain Z] {ι : Type*} [Finite ι] (P : ι → Set Z)
    (hcover : ∀ y : Z →ₐ[k] k, ∃ i, ∀ g ∈ P i, y g = 0) :
    ∃ i, ∀ y : Z →ₐ[k] k, ∀ g ∈ P i, y g = 0 := by
  classical
  by_contra hne
  push_neg at hne
  choose y g hg hyg using hne
  let : Fintype ι := Fintype.ofFinite ι
  have hprod : ∏ i, g i = 0 := by
    refine TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k) fun z => ?_
    obtain ⟨i, hi⟩ := hcover z
    rw [map_prod, map_zero]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hi _ (hg i))
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hprod
  exact hyg i (by rw [hi, map_zero])

end Dense

section Component


end Component

end CFSG.LieType.AlgebraicGroups.TorusConjugacy
