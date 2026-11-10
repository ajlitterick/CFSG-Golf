module

public import CFSG.RankThree.PartOne.S11d.FieldFFTwo
public import CFSG.RankThree.PartOne.Mult.Exceptional

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank Subgroup
open CFSG.RankThree.PartOne


theorem genericOrders_odd (t : StatedLieTag) (n m : ℕ) (hm : 1 ≤ m)
    (hn : t = .POmegaMinus → 1 ≤ n) (hne : t ≠ .POmegaOdd) :
    ¬ 2 ∣ (genericOrders t n 2 m).1 * (genericOrders t n 2 m).2 := by
  have hq : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hodd1 : Odd (2 ^ m - 1) := by
    obtain ⟨r, hr⟩ := hq
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    exact ⟨r - 1, by omega⟩
  have hodd2 : Odd (2 ^ m + 1) := hq.add_one
  have key : ∀ {a b : ℕ}, Odd b → a ∣ b → a % 2 = 1 := fun hb hab =>
    Nat.odd_iff.mp (Odd.of_dvd_nat hb hab)
  cases t <;> simp [genericOrders]
  · exact key hodd1 (Nat.gcd_dvd_right _ _)
  · exact key hodd2 (Nat.gcd_dvd_right _ _)
  · exact key hodd1 (Nat.gcd_dvd_right _ _)
  · exact hne rfl
  · simp [hq]
  · have hn1 := hn rfl
    have hev : Even ((2 ^ m) ^ n) := (Nat.even_pow.mpr ⟨hq, by omega⟩)
    exact key hev.add_one (Nat.gcd_dvd_right _ _)
  · exact key (by decide : Odd 3) (Nat.gcd_dvd_left _ _)
  · exact key hodd1 (Nat.gcd_dvd_right _ _)
  · exact key (by decide : Odd 3) (Nat.gcd_dvd_left _ _)


end CFSG.RankThree.PartOne.FieldFix
