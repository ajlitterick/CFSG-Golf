module

public import CFSG.Sporadic.HNOddCore.SylD

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem card_filter_fin_countP (n : ℕ) (p : ℕ → Bool) :
    (Finset.univ.filter fun k : Fin n => p k = true).card = (List.range n).countP p := by
  have h := card_filter_range_eq_countP' n (fun k => p k = true)
  simp only [Bool.decide_eq_true] at h
  rw [← h]
  refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨Finset.mem_range.2 k.2, by simpa using hk.2⟩
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨⟨i, hi.1⟩, by simpa using hi.2, rfl⟩

theorem card_fin_true (n : ℕ) (p : ℕ → Bool) :
    Nat.card {c : Fin n // p c = true} = (List.range n).countP p := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter_fin_countP]


theorem sub_orderOf_ne_four {G : Type*} [Group G] {H : Subgroup G} {a : H} (h : a ^ 2 = 1) :
    orderOf a ≠ 4 := by
  intro h4
  have := orderOf_dvd_of_pow_eq_one h
  rw [h4] at this
  exact absurd this (by norm_num)

theorem exists_cycleType_of_sq {σ : Perm (Fin 12)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    ∃ k, 1 ≤ k ∧ k ≤ 6 ∧ σ.cycleType = Multiset.replicate k 2 := by
  have hord : orderOf σ = 2 := orderOf_eq_prime h2 h1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (hord ▸ Nat.prime_two)
  rw [hord] at hn
  refine ⟨n + 1, by omega, ?_, hn⟩
  have hs := σ.sum_cycleType_le
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hs
  omega


theorem nine_iff
    (c : Fin 29) : (∀ y ∈ Pc, rho4 y = repPerm c → orderOf y = 4) ↔
    InvData.nonRep.contains pReps[(c : ℕ)]! = true := by
  constructor
  · intro h
    by_contra hn
    rw [Bool.not_eq_true] at hn
    have := h _ (liftC_mem _) (by rw [← ePerm_eq (rep_lt c.2)]; rfl)
    exact sub_orderOf_ne_four (rep_sq c.2 hn) this
  · intro h y _ hy
    exact nonRep_orderOf c.2 h hy


theorem card_nine :
    Nat.card {c : Fin 29 // ∀ y ∈ Pc, rho4 y = repPerm c → orderOf y = 4} = 9 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight nine_iff),
    card_fin_true 29 (fun c => InvData.nonRep.contains pReps[c]!)]
  exact wit_parts.2.2.2.2.2.1


end CFSG.Sporadic.HNOddCore
