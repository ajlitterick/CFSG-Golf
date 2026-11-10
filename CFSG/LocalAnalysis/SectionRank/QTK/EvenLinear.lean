module

public import CFSG.LocalAnalysis.SectionRank.QTK.List
public import CFSG.LocalAnalysis.SectionRank.QTK.Basic
import CFSG.LocalAnalysis.SectionRank.QTK.EvenBlocks3
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem three_dvd_two_pow_add_one {f : ℕ} (hf : Odd f) : 3 ∣ 2 ^ f + 1 := by
  obtain ⟨k, rfl⟩ := hf
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [Nat.dvd_iff_mod_eq_zero, pow_succ, pow_mul]
  norm_num
  omega

theorem exists_prime_ne_five_dvd_two_pow_add_one {f : ℕ} (hf : 1 ≤ f) (hf2 : f ≠ 2) :
    ∃ r, r.Prime ∧ r ≠ 2 ∧ r ≠ 5 ∧ r ∣ 2 ^ f + 1 := by
  rcases Nat.even_or_odd f with ⟨k, hk⟩ | hodd
  · obtain ⟨r, hr, hr7, hrd⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_prime_seven_le_dvd_two_pow_add_one (f := f) (by omega)
    exact ⟨r, hr, by omega, by omega, hrd⟩
  · exact ⟨3, Nat.prime_three, by norm_num, by norm_num, three_dvd_two_pow_add_one hodd⟩


end CFSG.SectionRank.QTK
