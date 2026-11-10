module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

theorem selfAdjoint_isometry_exhaustion (h2 : (2 : K) ≠ 0)
    (g : TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) :
    ∃ A : symplecticSimilitudes K, g = selfAdjointOrthogonalAction h2 A ∨
      g = selfAdjointOrthogonalAction h2 A *
        QuadraticMap.negOrthogonal (selfAdjointForm K) := by
  obtain ⟨⟨A, ε⟩, rfl⟩ := selfAdjointFullAction_surjective h2 g
  refine ⟨A, ?_⟩
  have hs : ε.val = 1 ∨ ε.val = -1 :=
    Units.eq_or_eq_neg_of_sq_eq_sq ε.val 1
      (by
        apply Units.ext
        rw [pow_two, one_pow]
        change (ε.val : K) * (ε.val : K) = 1
        simpa only [pow_two] using (mem_rootsOfUnity' 2 ε.val).mp ε.property)
  rcases hs with hε | hε
  · have he : ε = 1 := Subtype.ext hε
    apply Or.inl
    change selfAdjointOrthogonalAction h2 A * selfAdjointScalarAction ε = _
    rw [he, map_one, mul_one]
  · have he : ε = selfAdjointNegSign K := Subtype.ext hε
    apply Or.inr
    change selfAdjointOrthogonalAction h2 A * selfAdjointScalarAction ε = _
    rw [he, selfAdjointScalarAction_neg]


end CFSG.ComponentClassification.CatalogueBOrthogonalFive
