module

public import CFSG.GroupTheory.HallHigmanPiCore

public section

namespace CFSG.HallHigman

universe u

open Subgroup


private abbrev PNum (ρ : Set Nat.Primes) (n : ℕ) : Prop := ∀ r : Nat.Primes, r.val ∣ n → r ∈ ρ

private theorem PNum.dvd {ρ : Set Nat.Primes} {m n : ℕ} (h : PNum ρ n) (hmn : m ∣ n) :
    PNum ρ m := fun r hr => h r (hr.trans hmn)

private theorem PNum.mul {ρ : Set Nat.Primes} {m n : ℕ} (hm : PNum ρ m) (hn : PNum ρ n) :
    PNum ρ (m * n) := fun r hr => by
  rcases (Nat.Prime.dvd_mul r.2).1 hr with h | h
  exacts [hm r h, hn r h]

private theorem PNum.one (ρ : Set Nat.Primes) : PNum ρ 1 := fun r hr =>
  absurd (Nat.le_of_dvd one_pos hr) (not_le.2 r.2.one_lt)


end CFSG.HallHigman
