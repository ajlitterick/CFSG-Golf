module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section NumberTheory

theorem dvd_sub_one_of_pow_dvd_pow_sub_one {p s e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hs : 1 ≤ s) (h : p ^ s ∣ e ^ p - 1) : p ∣ e - 1 ∧ p ^ (s - 1) ∣ e - 1 := by
  have hpe : p ∣ e ^ p - 1 := (dvd_pow_self p (by omega : s ≠ 0)).trans h
  have hep : 1 ≤ e ^ p := Nat.one_le_pow _ _ he
  have h1 : p ∣ e - 1 := by
    have hz := (ZMod.natCast_eq_zero_iff (e ^ p - 1) p).mpr hpe
    rw [Nat.cast_sub hep, Nat.cast_pow, ZMod.pow_card, Nat.cast_one, sub_eq_zero] at hz
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub he, Nat.cast_one, hz, sub_self]
  refine ⟨h1, ?_⟩
  rcases he.lt_or_eq with he1 | rfl
  · have hne : ¬ p ∣ e := fun hd => by
      have := Nat.dvd_sub hd h1
      rw [Nat.sub_sub_self he] at this
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
    have hlte := padicValNat.pow_sub_pow (hp.out.odd_of_ne_two hp2) he1 h1 hne
      (n := p) hp.out.ne_zero
    rw [one_pow, padicValNat_self] at hlte
    have hne0 : e ^ p - 1 ≠ 0 := by
      have : 1 < e ^ p := Nat.one_lt_pow hp.out.ne_zero he1
      omega
    have hle := (padicValNat_dvd_iff_le hne0).mp h
    rw [hlte] at hle
    exact (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
  · simp

theorem one_add_pow_modEq (N j : ℕ) : (1 + N) ^ j ≡ 1 + j * N [MOD N ^ 2] := by
  induction j with
  | zero => simp [Nat.ModEq]
  | succ j ih =>
    have e : (1 + j * N) * (1 + N) = 1 + (j + 1) * N + j * N ^ 2 := by ring
    calc (1 + N) ^ (j + 1) = (1 + N) ^ j * (1 + N) := pow_succ _ _
      _ ≡ (1 + j * N) * (1 + N) [MOD N ^ 2] := ih.mul_right _
      _ = 1 + (j + 1) * N + j * N ^ 2 := e
      _ ≡ 1 + (j + 1) * N [MOD N ^ 2] := Nat.add_mul_mod_self_right _ _ _

theorem one_add_mul_pow_pow_modEq {p s c j : ℕ} (hs : 2 ≤ s) (hcj : c * j % p = 1) :
    (1 + c * p ^ (s - 1)) ^ j ≡ 1 + p ^ (s - 1) [MOD p ^ s] := by
  have hdvd : p ^ s ∣ (c * p ^ (s - 1)) ^ 2 := by
    have h1 : p ^ s ∣ p ^ (2 * (s - 1)) := pow_dvd_pow p (by omega)
    have h2 : p ^ (2 * (s - 1)) ∣ (c * p ^ (s - 1)) ^ 2 := ⟨c ^ 2, by ring⟩
    exact h1.trans h2
  have h3 := (one_add_pow_modEq (c * p ^ (s - 1)) j).of_dvd hdvd
  have e : 1 + j * (c * p ^ (s - 1)) = 1 + p ^ (s - 1) + (c * j / p) * p ^ s := by
    have hdm := Nat.div_add_mod (c * j) p
    rw [hcj] at hdm
    have hps : p ^ s = p * p ^ (s - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    calc 1 + j * (c * p ^ (s - 1)) = 1 + (c * j) * p ^ (s - 1) := by ring
      _ = 1 + (p * (c * j / p) + 1) * p ^ (s - 1) := by rw [hdm]
      _ = 1 + p ^ (s - 1) + (c * j / p) * p ^ s := by rw [hps]; ring
  rw [e] at h3
  exact h3.trans (Nat.add_mul_mod_self_right _ _ _)

end NumberTheory


end CFSG.StandardType

end
