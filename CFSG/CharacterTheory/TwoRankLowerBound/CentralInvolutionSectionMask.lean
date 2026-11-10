module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralSectionSwitch
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionMask

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem two_primary_regular_odd_iff {G : Type*} [Group G]
    (primary regular : G) (exponent : ℕ)
    (hprimary : orderOf primary ∣ 2 ^ exponent)
    (hregular : Nat.Coprime 2 (orderOf regular)) (hcommute : Commute primary regular) :
    Odd (orderOf (primary * regular)) ↔ primary = 1 := by
  have hcoprime : Nat.Coprime (orderOf primary) (orderOf regular) :=
    (hregular.pow_left exponent).of_dvd_left hprimary
  rw [hcommute.orderOf_mul_eq_mul_orderOf_of_coprime hcoprime]
  constructor
  · intro hodd
    have hoddPrimary := hodd.of_dvd_nat (dvd_mul_right (orderOf primary) (orderOf regular))
    exact orderOf_eq_one_iff.mp ((hoddPrimary.coprime_two_right.pow_right exponent).eq_one_of_dvd hprimary)
  · intro hequal
    rw [hequal, orderOf_one, one_mul]
    exact Nat.coprime_two_left.mp hregular


theorem oddOrderElements_primeSectionUnion {G : Type*} [Group G] :
    primeSectionUnion 2 {element : G | Odd (orderOf element)} := by
  intro leftPrimary rightPrimary leftRegular rightRegular leftExponent rightExponent
    hleftPrimary hrightPrimary hleftRegular hrightRegular hleftCommute hrightCommute hconjugate
  change Odd (orderOf (leftPrimary * leftRegular)) ↔ Odd (orderOf (rightPrimary * rightRegular))
  rw [two_primary_regular_odd_iff leftPrimary leftRegular leftExponent hleftPrimary hleftRegular hleftCommute,
    two_primary_regular_odd_iff rightPrimary rightRegular rightExponent hrightPrimary hrightRegular hrightCommute]
  constructor
  · intro hequal
    exact isConj_one_right.mp (hequal ▸ hconjugate)
  · intro hequal
    exact isConj_one_left.mp (hequal ▸ hconjugate)

end CFSG.TwoRankLowerBound.Helpers
