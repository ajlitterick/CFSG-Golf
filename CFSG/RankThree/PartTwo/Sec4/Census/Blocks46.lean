module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.LocalAnalysis.SectionRank.QTK.EvenBlocks3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven
open CFSG.RankThree.PartTwo.Census (threeCycleMat threeCycleMat_pow_three threeCycleMat_pow_val_add
  threeCycleMat_pow_val_zero_one det_threeCycleMat eq_one_of_mul_self_eq_one isElemAbelian_range
  le_localRank_quotient_of_le_normalizer le_normalizer_of_conj_mem pslReindex
  localRank_eq_of_mulEquiv)

variable {K : Type} [Field K] [CharP K 2]


theorem three_le_localRank_PSL_of_six_le [Finite K] {n : ℕ} (hn : 6 ≤ n) :
    3 ≤ localRank 3 (ProjectiveSpecialLinearGroup (Fin n) K) :=
  CFSG.SectionRank.QTK.three_le_localRank_PSL_of_six_le hn

theorem three_le_localRank_projSL_two {n : ℕ} (hn : 6 ≤ n) [Finite (projSL n (GaloisField 2 1))] :
    3 ≤ localRank 3 (projSL n (GaloisField 2 1)) := by
  rw [← localRank_eq_of_mulEquiv (pslEquivProjSL n (GaloisField 2 1)) Nat.prime_three]
  exact three_le_localRank_PSL_of_six_le hn

end CFSG.RankThree.PartTwo.Sec4.Census
