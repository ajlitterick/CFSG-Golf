module

public import CFSG.GroupTheory.SteinbergCBFTCores

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup CFSG.HallHigman

section Cores

variable {X : Type*} [Group X]

@[expose] noncomputable def coreAbove (π : Set Nat.Primes) (N : Subgroup X) : Subgroup X :=
  (piCore π (X ⧸ N.normalCore)).comap (QuotientGroup.mk' N.normalCore)

instance coreAbove_normal (π : Set Nat.Primes) (N : Subgroup X) : (coreAbove π N).Normal :=
  Subgroup.Normal.comap inferInstance _

@[expose] def IsPrimeSetNumber (π : Set Nat.Primes) (n : ℕ) : Prop :=
  ∀ r : Nat.Primes, r.val ∣ n → r ∈ π


variable [Finite X]


end Cores

section Series

@[expose] def upperPrimes (p n : ℕ) : Set Nat.Primes :=
  if Even n then {q | q.val ≠ p} else {q | q.val = p}

@[expose] noncomputable def upperPSeries (p : ℕ) (X : Type*) [Group X] : ℕ → Subgroup X
  | 0 => ⊥
  | n + 1 => coreAbove (upperPrimes p n) (upperPSeries p X n)


variable {X : Type*} [Group X]

instance upperPSeries_normal (p n : ℕ) : (upperPSeries p X n).Normal := by
  cases n with
  | zero => exact normal_bot
  | succ n => exact coreAbove_normal _ _

@[expose] def HasPSeries (p : ℕ) (X : Type*) [Group X] (n : ℕ) : Prop :=
  ∃ N : ℕ → Subgroup X, N 0 = ⊥ ∧ N n = ⊤ ∧ ∀ i < n, (N (i + 1)).Normal ∧ N i ≤ N (i + 1) ∧
    IsPrimeSetNumber (upperPrimes p i) ((N i).relIndex (N (i + 1)))


theorem HasPSeries.of_mulEquiv {Y : Type*} [Group Y] {p n : ℕ} (e : X ≃* Y)
    (h : HasPSeries p X n) : HasPSeries p Y n := by
  obtain ⟨N, h0, htop, h⟩ := h
  refine ⟨fun i => (N i).map e.toMonoidHom, by show map _ (N 0) = ⊥; rw [h0, Subgroup.map_bot], by
    show map _ (N n) = ⊤
    rw [htop, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.2 e.surjective, fun i hi => ?_⟩
  obtain ⟨hn, hle, hidx⟩ := h i hi
  refine ⟨hn.map _ e.surjective, map_mono hle, ?_⟩
  rw [relIndex_map_map_of_injective _ _ e.injective]
  exact hidx

end Series

section Numbers

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]


theorem IsPrimeSetNumber.dvd {π : Set Nat.Primes} {m n : ℕ} (h : IsPrimeSetNumber π n)
    (hmn : m ∣ n) : IsPrimeSetNumber π m := fun r hr => h r (hr.trans hmn)

theorem IsPrimeSetNumber.mul {π : Set Nat.Primes} {m n : ℕ} (hm : IsPrimeSetNumber π m)
    (hn : IsPrimeSetNumber π n) : IsPrimeSetNumber π (m * n) := fun r hr =>
  ((Nat.Prime.dvd_mul r.2).1 hr).elim (hm r) (hn r)


end Numbers

section PLengthCount


end PLengthCount

end CFSG.GroupTheory.FT63ChII
