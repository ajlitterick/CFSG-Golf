module

public import CFSG.ClassicalInvolution.Q3.Q3WACore

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic
  (Commutes FundamentalSingleClass fundamentalSubgroups modelUniv)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
  (isHyperbolicPlane_stdPlane longBlock planeGroup_stdPlane stdPlane)

theorem orderOf_not_dvd_three_of_center_sp {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    {g : StatedSp n K} (hg : g ∈ Subgroup.center (StatedSp n K)) : ¬ 3 ∣ orderOf g := by
  have h2 : g * g = 1 := Models.SymplecticPairs.mul_self_eq_one_of_mem_center hn hg
  have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  intro h3
  have := Nat.le_of_dvd (by norm_num) (h3.trans hord)
  omega

theorem statedLieAdmissible_psp2 : StatedLieAdmissible .PSp 2 3 1 :=
  ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩


theorem finite_psp2 : Finite (modelUniv .PSp 2 3 1 Nat.prime_three).K :=
  inferInstanceAs (Finite (StatedSp 2 (GaloisField 3 1)))


theorem fundamentalSingleClass_psp2 :
    FundamentalSingleClass .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D :=
  ModelFacts.fundamentalSingleClass .PSp 2 3 1 Nat.prime_three trivial statedLieAdmissible_psp2
    (by decide) (by decide)


end CFSG.ClassicalInvolution.Q3.Q3Z
