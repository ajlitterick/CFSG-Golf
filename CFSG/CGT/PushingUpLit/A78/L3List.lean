module

public import CFSG.CGT.PushingUpLit.A78.L3WC
import CFSG.Adapters.WholeGroupLayer
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Foundations.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.ARS

variable {G : Type} [Group G] [Finite G] {J V V₂ Z : Subgroup G} {e : ℕ}

section Sylow


end Sylow

section Orders

theorem two_pow_dvd_card_psl' {K : Type} [Field K] [Finite K] {f m : ℕ}
    (hK : Nat.card K = 2 ^ f) (hm : 2 ≤ m) :
    2 ^ (f * (m * (m - 1) / 2)) ∣
      Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL m K)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega)]
  have hgP : Nat.gcd m (Nat.card K - 1) ∣ ∏ j ∈ Finset.Icc 2 m, (Nat.card K ^ j - 1) := by
    have h1 : Nat.gcd m (Nat.card K - 1) ∣ Nat.card K - 1 := Nat.gcd_dvd_right _ _
    have h2 : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2
    have h3 : Nat.card K ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 m, (Nat.card K ^ j - 1) :=
      Finset.dvd_prod_of_mem (fun j => Nat.card K ^ j - 1) (Finset.mem_Icc.2 ⟨le_refl 2, hm⟩)
    exact h1.trans (h2.trans h3)
  have hq : Nat.card K ^ (m * (m - 1) / 2) = 2 ^ (f * (m * (m - 1) / 2)) := by
    rw [hK, ← pow_mul]
  rw [Nat.mul_div_assoc _ hgP, hq]
  exact Dvd.intro _ rfl

end Orders

section Endgame


end Endgame

end CFSG.CGT.PushingUpLit.A78
