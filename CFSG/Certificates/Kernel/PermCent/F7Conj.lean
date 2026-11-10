module

public import CFSG.GH74.GLS.C3.Prop121.Card7Defs

public section

namespace CFSG.Certificates.Kernel.F7Conj

open Equiv Equiv.Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Prop121.Card7

theorem val_mul (a b : F7) : ((a * b : F7) : Amb 7) = (a : Amb 7) * (b : Amb 7) := rfl

theorem val_inv (a : F7) : ((a⁻¹ : F7) : Amb 7) = (a : Amb 7)⁻¹ := rfl

theorem val_pow (a : F7) (k : ℕ) : ((a ^ k : F7) : Amb 7) = (a : Amb 7) ^ k :=
  Subgroup.coe_pow _ _ _

theorem sign_eq (f : F7) : sign (f : Amb 7).1 = sign (f : Amb 7).2 := f.2.2

theorem comm_x4 (f : F7) : (f : Amb 7).2 * x4 = x4 * (f : Amb 7).2 := f.2.1

theorem fst_pow (f : F7) (k : ℕ) : ((f ^ k : F7) : Amb 7).1 = (f : Amb 7).1 ^ k := by
  rw [val_pow, Prod.pow_fst]

theorem snd_pow (f : F7) (k : ℕ) : ((f ^ k : F7) : Amb 7).2 = (f : Amb 7).2 ^ k := by
  rw [val_pow, Prod.pow_snd]

theorem fst_ne_one {f : F7} (h1 : f ≠ 1) (h2 : (f : Amb 7).2 = 1) : (f : Amb 7).1 ≠ 1 := by
  intro h
  apply h1
  apply Subtype.ext
  exact Prod.ext h h2

theorem exists_conj_of_cycleType {f g : F7} (hf : (f : Amb 7).2 = 1) (hg : (g : Amb 7).2 = 1)
    (h : (f : Amb 7).1.cycleType = (g : Amb 7).1.cycleType) : ∃ k : F7, k * f * k⁻¹ = g := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 h)
  let e : Perm (Fin 4) := if sign c = 1 then 1 else swap 0 1
  have he : e * x4 = x4 * e := by
    by_cases hs : sign c = 1
    · simp [e, hs]
    · simp only [e, if_neg hs]
      decide
  have hse : sign c = sign e := by
    by_cases hs : sign c = 1
    · simp [e, hs]
    · simp only [e, if_neg hs]
      rw [sign_swap (by decide)]
      rcases Int.units_eq_one_or (sign c) with h' | h'
      · exact absurd h' hs
      · exact h'
  refine ⟨⟨(c, e), he, hse⟩, ?_⟩
  apply Subtype.ext
  rw [val_mul, val_mul, val_inv]
  refine Prod.ext ?_ ?_
  · exact hc
  · simp [hf, hg]

theorem cycleType_of_pow_prime {m p : ℕ} [hp : Fact p.Prime] {r : Perm (Fin m)} (h : r ^ p = 1)
    (h1 : r ≠ 1) : ∃ k, r.cycleType = Multiset.replicate (k + 1) p ∧ numMoved r = (k + 1) * p := by
  have ho : orderOf r = p := orderOf_eq_prime h h1
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ hp.out)
  rw [ho] at hk
  refine ⟨k, hk, ?_⟩
  rw [numMoved_eq_card_support, ← sum_cycleType, hk, Multiset.sum_replicate, smul_eq_mul]

theorem numMoved_le {m : ℕ} (r : Perm (Fin m)) : numMoved r ≤ m := by
  rw [numMoved_eq_card_support]
  exact (Finset.card_le_univ _).trans (Fintype.card_fin m).le


theorem sign_of_cycleType_two {m k : ℕ} {r : Perm (Fin m)}
    (hk : r.cycleType = Multiset.replicate (k + 1) 2) : sign r = (-1) ^ (3 * (k + 1)) := by
  rw [sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  congr 1
  ring


theorem numMoved_one {m : ℕ} : numMoved (1 : Perm (Fin m)) = 0 := by
  rw [numMoved_eq_card_support, support_one, Finset.card_empty]

theorem cycleType_of_pow_three {m j : ℕ} {r : Perm (Fin m)} (h3 : r ^ 3 = 1)
    (hn : numMoved r = 3 * j) (hj : 0 < j) : r.cycleType = Multiset.replicate j 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : r ≠ 1 := by
    rintro rfl
    rw [numMoved_one] at hn
    omega
  obtain ⟨k, hk, hm⟩ := cycleType_of_pow_prime h3 h1
  have hkj : k + 1 = j := by omega
  rw [hk, hkj]

theorem numMoved_sign_of_sq {m : ℕ} {r : Perm (Fin m)} (h2 : r ^ 2 = 1) :
    ∃ a, numMoved r = 2 * a ∧ sign r = (-1) ^ a := by
  by_cases h1 : r = 1
  · subst h1
    exact ⟨0, numMoved_one, by simp⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk, hm⟩ := cycleType_of_pow_prime h2 h1
    refine ⟨k + 1, by rw [hm]; ring, ?_⟩
    have h3 : ((-1 : ℤˣ) ^ 3) = -1 := by decide
    rw [sign_of_cycleType_two hk, pow_mul, h3]

theorem eq_one_of_numMoved {m : ℕ} {r : Perm (Fin m)} (h : numMoved r = 0) : r = 1 :=
  card_support_eq_zero.1 h


end CFSG.Certificates.Kernel.F7Conj

end
