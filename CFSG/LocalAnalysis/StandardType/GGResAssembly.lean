module

public import CFSG.LocalAnalysis.StandardType.GGRCCaseII

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem tablePRow_E6_field {p : ℕ} {J X : LargeEvenLabel} (h : GGTablePRow p J X)
    (hJ : J.tag = .A ∨ J.tag = .twA) (hJr : J.rank = 5) (hX : X.tag = .E6 ∨ X.tag = .twE6) :
    X.n = J.n ∨ (J.tag = .twA ∧ X.tag = .twE6 ∧ 3 * X.n = J.n) := by
  obtain ⟨tJ, rJ, nJ⟩ := J
  obtain ⟨tX, rX, nX⟩ := X
  simp only at hJ hJr hX ⊢
  subst hJr
  simp only [GGTablePRow, LargeEvenLabel.mk.injEq] at h
  rcases hJ with rfl | rfl <;> rcases hX with rfl | rfl <;> simp_all <;> omega

end CFSG.StandardType
