module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.GeneratedCore

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem isElemAbelian_isPGroup {G : Type u} [Group G] (prime : ℕ)
    (subgroup : Subgroup G) (hab : IsElemAbelian prime subgroup) : IsPGroup prime subgroup := by
  apply IsPGroup.of_exponent_dvd_pow (n := 1)
  rw [pow_one]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro element
  apply Subtype.ext
  exact hab.2 element element.property


end CFSG.RankThreeEvenClassification.Helpers
