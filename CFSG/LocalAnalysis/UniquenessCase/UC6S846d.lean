module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10
public import CFSG.LocalAnalysis.UniquenessCase.UCKU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h : 4 ^ k ≡ 1 [MOD 3] := by
    simpa using (Nat.ModEq.pow k (show 4 ≡ 1 [MOD 3] by decide))
  have h2 : 2 ^ (2 * k + 1) + 1 = 2 * 4 ^ k + 1 := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [h2]
  have h3 := Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 2 h)
  exact (Nat.modEq_zero_iff_dvd).1 (h3.trans (by decide))

theorem lift_maximal {H K : Type*} [Group H] [Group K] [Finite H] (f : H →* K) {q : ℕ}
    (SL : Subgroup H) (S : Subgroup K) (hmap : SL.map f = S) (hdisj : Disjoint SL f.ker)
    (hker : IsPGroup 2 f.ker) (hq : q.Prime) (hq2 : q ≠ 2)
    (hmax : ∀ T : Subgroup K, IsPGroup q T → S ≤ T → T = S) (hSL : IsPGroup q SL) :
    ∀ T : Subgroup H, IsPGroup q T → SL ≤ T → T = SL := by
  intro T hT hSLT
  have hTdisj : Disjoint T f.ker := by
    rw [Subgroup.disjoint_def]
    intro x hxT hxker
    obtain ⟨a, ha⟩ := hT ⟨x, hxT⟩
    obtain ⟨b, hb⟩ := hker ⟨x, hxker⟩
    have ha' : x ^ q ^ a = 1 := by simpa using ha
    have hb' : x ^ 2 ^ b = 1 := by simpa using hb
    have hcop : Nat.Coprime (q ^ a) (2 ^ b) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
    have h1 : orderOf x ∣ Nat.gcd (q ^ a) (2 ^ b) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha') (orderOf_dvd_of_pow_eq_one hb')
    rw [hcop.gcd_eq_one] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  have hTq : IsPGroup q (T.map f) := hT.map f
  have hST : S ≤ T.map f := hmap ▸ Subgroup.map_mono hSLT
  have hTS : T.map f = S := hmax _ hTq hST
  have hcard : Nat.card T = Nat.card SL := by
    rw [← card_map_of_disjoint_ker f T hTdisj, ← card_map_of_disjoint_ker f SL hdisj, hTS, hmap]
  exact (Subgroup.eq_of_le_of_card_ge hSLT (by rw [hcard])).symm


end CFSG.LocalAnalysis.UniquenessCase.UC6S846
