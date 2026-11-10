module

public import CFSG.LocalAnalysis.StandardType.GGPresentationWeyl
public import CFSG.LieType.Universal.Catalog
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank

theorem ggStandardCopy_PSL (n f : ℕ) (hadm : StatedLieAdmissible .PSL n 2 f)
    (hrank : 3 ≤ bnRank .PSL n) : ∃ ν, GGStandardCopy (lieUniversal .PSL n 2 f hadm.1).D ν := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [bnRank] at hrank; omega⟩
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  exact ⟨slWeylLift m h2, slWeylLift_standardCopy m h2⟩

end CFSG.StandardType
