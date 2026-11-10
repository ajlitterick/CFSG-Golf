module

public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin
open scoped BigOperators

private theorem toAdd_allOnes_zpow (k : ℤ) (i : Fin 12) :
    Multiplicative.toAdd (G6.allOnes 12 ^ k) i = (k : ZMod 2) := by
  simp [G6.allOnes, toAdd_zpow]

private theorem intCast_two_mul (j : ℤ) : ((2 * j : ℤ) : ZMod 2) = 0 := by
  rw [Int.cast_mul, Int.cast_ofNat]
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

private theorem intCast_two_mul_add_one (j : ℤ) : ((2 * j + 1 : ℤ) : ZMod 2) = 1 := by
  rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]

private theorem mem_zpowers_allOnes_iff (z : G6.PermMod 12) :
    z ∈ Subgroup.zpowers (G6.allOnes 12) ↔
      Multiplicative.toAdd z = 0 ∨ ∀ i, Multiplicative.toAdd z i = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
    · left
      funext i
      rw [hj, toAdd_allOnes_zpow]
      exact intCast_two_mul j
    · right
      intro i
      rw [hj, toAdd_allOnes_zpow]
      exact intCast_two_mul_add_one j
  · rintro (h0 | h1)
    · refine ⟨0, ?_⟩
      apply Multiplicative.toAdd.injective
      simpa using h0.symm
    · refine ⟨1, ?_⟩
      apply Multiplicative.toAdd.injective
      funext i
      rw [toAdd_allOnes_zpow]
      simp [h1 i]

private theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide


private theorem toAdd_comm (σ : Equiv.Perm (Fin 12)) (x : G6.PermMod 12) (i : Fin 12) :
    Multiplicative.toAdd (G6.permAct 12 σ x * x⁻¹) i =
      Multiplicative.toAdd x (σ⁻¹ i) + Multiplicative.toAdd x i := by
  rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply]
  rcases zmod2_eq_zero_or_one (Multiplicative.toAdd x i) with h | h
  · rw [h, show (-(0 : ZMod 2)) = 0 by decide]
  · rw [h, show (-(1 : ZMod 2)) = 1 by decide]

private def evec (p : Fin 12) : Fin 12 → ZMod 2 := fun i => if i = p then 1 else 0

private def pairVec (p q : Fin 12) : G6.PermMod 12 :=
  Multiplicative.ofAdd (evec p + evec q)

private theorem toAdd_pairVec (p q i : Fin 12) :
    Multiplicative.toAdd (pairVec p q) i = evec p i + evec q i := rfl

private theorem pairVec_mem_coreMod (p q : Fin 12) (hpq : p ≠ q) :
    pairVec p q ∈ G6.coreMod 12 := by
  rw [G6.mem_coreMod]
  simp only [toAdd_pairVec, Pi.add_apply]
  rw [Finset.sum_add_distrib]
  have hp : ∑ i, evec p i = 1 := by
    rw [Finset.sum_eq_single p]
    · simp [evec]
    · intro b _ hb; simp [evec, hb]
    · intro hp'; exact absurd (Finset.mem_univ p) hp'
  have hq : ∑ i, evec q i = 1 := by
    rw [Finset.sum_eq_single q]
    · simp [evec]
    · intro b _ hb; simp [evec, hb]
    · intro hq'; exact absurd (Finset.mem_univ q) hq'
  rw [hp, hq]
  exact CharTwo.add_self_eq_zero 1

private theorem toAdd_pairVec_self_left (p q : Fin 12) (hpq : p ≠ q) :
    Multiplicative.toAdd (pairVec p q) p = 1 := by
  rw [toAdd_pairVec]
  simp [evec, hpq]

private theorem toAdd_pairVec_eq_one_iff {p q : Fin 12} (hpq : p ≠ q) {i : Fin 12} :
    Multiplicative.toAdd (pairVec p q) i = 1 ↔ i = p ∨ i = q := by
  rw [toAdd_pairVec]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    rw [evec, if_neg hc.1, evec, if_neg hc.2, add_zero] at h
    exact zero_ne_one h
  · rintro (rfl | rfl)
    · simp [evec, hpq]
    · simp [evec, hpq.symm]

theorem eq_one_of_mem_zpowers_allOnes (σ : Equiv.Perm (Fin 12))
    (h : ∀ x ∈ G6.coreMod 12,
      G6.permAct 12 σ x * x⁻¹ ∈ Subgroup.zpowers (G6.allOnes 12)) :
    σ = 1 := by
  have key : ∀ i j : Fin 12, i ≠ j →
      Multiplicative.toAdd (G6.permAct 12 σ (pairVec i j) * (pairVec i j)⁻¹) = 0 := by
    intro i j hij
    have hz := h (pairVec i j) (pairVec_mem_coreMod i j hij)
    rcases (mem_zpowers_allOnes_iff _).mp hz with h0 | h1
    · exact h0
    · exfalso
      have hcard : ({i, j, σ i, σ j} : Finset (Fin 12)).card < 12 := by
        have hle := Finset.card_le_four (a := i) (b := j) (c := σ i) (d := σ j)
        omega
      obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := ({i, j, σ i, σ j} : Finset (Fin 12))) (t := Finset.univ) hcard
      have hpi : p ≠ i := fun hh => hp (by simp [hh])
      have hpj : p ≠ j := fun hh => hp (by simp [hh])
      have hpsi : p ≠ σ i := fun hh => hp (by simp [hh])
      have hpsj : p ≠ σ j := fun hh => hp (by simp [hh])
      have hzero : Multiplicative.toAdd
          (G6.permAct 12 σ (pairVec i j) * (pairVec i j)⁻¹) p = 0 := by
        rw [toAdd_comm, toAdd_pairVec, toAdd_pairVec]
        have h1p : evec i p + evec j p = 0 := by
          show (if p = i then (1 : ZMod 2) else 0) + (if p = j then 1 else 0) = 0
          rw [if_neg hpi, if_neg hpj, add_zero]
        have hne1 : σ⁻¹ p ≠ i := by
          intro hh; apply hpsi
          have := congrArg σ hh
          simpa using this
        have hne2 : σ⁻¹ p ≠ j := by
          intro hh; apply hpsj
          have := congrArg σ hh
          simpa using this
        have h2p : evec i (σ⁻¹ p) + evec j (σ⁻¹ p) = 0 := by
          show (if σ⁻¹ p = i then (1 : ZMod 2) else 0) +
            (if σ⁻¹ p = j then 1 else 0) = 0
          rw [if_neg hne1, if_neg hne2, add_zero]
        rw [h1p, h2p, add_zero]
      have hp1 : Multiplicative.toAdd
          (G6.permAct 12 σ (pairVec i j) * (pairVec i j)⁻¹) p = 1 := h1 p
      rw [hzero] at hp1
      exact zero_ne_one hp1
  have hfix : ∀ i : Fin 12, σ⁻¹ i = i := by
    intro i
    have hex : ∃ j k : Fin 12, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
      fin_cases i <;> decide
    obtain ⟨j, k, hj, hk, hjk⟩ := hex
    have h1 := congrFun (key i j hj.symm) i
    have h2 := congrFun (key i k hk.symm) i
    rw [toAdd_comm, toAdd_pairVec_self_left i j hj.symm] at h1
    rw [toAdd_comm, toAdd_pairVec_self_left i k hk.symm] at h2
    have hj' : Multiplicative.toAdd (pairVec i j) (σ⁻¹ i) = 1 := by
      have h := eq_neg_of_add_eq_zero_left h1
      rw [show (-1 : ZMod 2) = 1 by decide] at h
      exact h
    have hk' : Multiplicative.toAdd (pairVec i k) (σ⁻¹ i) = 1 := by
      have h := eq_neg_of_add_eq_zero_left h2
      rw [show (-1 : ZMod 2) = 1 by decide] at h
      exact h
    rcases (toAdd_pairVec_eq_one_iff hj.symm).mp hj' with h | h
    · exact h
    · rcases (toAdd_pairVec_eq_one_iff hk.symm).mp hk' with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hjk
  have hinv : σ⁻¹ = 1 := Equiv.ext hfix
  exact inv_eq_one.mp hinv


end CFSG.Quasithin.AppendixH.H11
