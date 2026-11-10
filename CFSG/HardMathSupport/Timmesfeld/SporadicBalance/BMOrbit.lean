module

public import CFSG.Assembly.Defs
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Sporadic.SmallOddCore

variable {p : ℕ} {S : Type*} [Group S]

theorem dvd_card_of_forall_dvd_card_orbit {G X : Type*} [Group G] [MulAction G X] [Finite X]
    {n : ℕ} (h : ∀ x : X, n ∣ Nat.card (MulAction.orbit G x)) : n ∣ Nat.card X := by
  classical
  have : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits G X), Nat.card_sigma]
  exact Finset.dvd_sum fun ω _ => h _

theorem pow_dvd_of_le_of_dvd_pow (hp : p.Prime) {n a k : ℕ} (hn : n ∣ p ^ a) (hk : p ^ k ≤ n) :
    p ^ k ∣ n := by
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hn
  refine pow_dvd_pow p ?_
  by_contra hjk
  have : p ^ j < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
