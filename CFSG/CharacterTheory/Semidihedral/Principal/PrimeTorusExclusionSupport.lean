module

public import CFSG.CharacterTheory.Semidihedral.Principal.NormalPrimeDihedralEightInvolutionCounts
public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.OrderFormula
public import CFSG.Adapters.LinearSmallCatalog

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

namespace PrimeTorusExclusion

theorem dvd_add_of_rotation_values {G : Type*} [Group G] (data : FiniteComplexRepresentation G)
    {r : G} {M : ℕ} (hMpos : 0 < M) (hM4 : 4 ∣ M) (hr : r ^ M = 1) (ε : ℤ)
    (ht : data.character (r ^ (M / 2)) = -ε)
    (hrot : ∀ v : ℤ, ¬ v ≡ 0 [ZMOD M] → ¬ v ≡ ((M / 2 : ℕ) : ℤ) [ZMOD M] →
      data.character (r ^ v) = -ε * (-1 : ℂ) ^ v) :
    (M : ℤ) ∣ (Module.finrank ℂ data.vector : ℤ) + ε := by
  obtain ⟨m, hm⟩ := cyclicMultiplicity_natural data r hMpos hr 0
  unfold cyclicMultiplicity at hm
  simp only [zero_mul, neg_zero, zpow_zero, mul_one] at hm
  have hhalf : M / 2 ∈ Finset.range M := Finset.mem_range.mpr (by omega)
  have hzero : 0 ∈ (Finset.range M).erase (M / 2) := by
    rw [Finset.mem_erase, Finset.mem_range]
    omega
  have hval : ∀ v ∈ ((Finset.range M).erase (M / 2)).erase 0,
      data.character (r ^ v) = -ε * (-1 : ℂ) ^ v := by
    intro v hv
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_range] at hv
    obtain ⟨hv0, hvh, hvM⟩ := hv
    have h := hrot (v : ℤ) (by
      intro hc
      have h1 : (v : ℤ) % M = 0 % M := hc
      rw [Int.emod_eq_of_lt (by omega) (by omega), Int.zero_emod] at h1
      omega) (by
      intro hc
      have h1 : (v : ℤ) % M = ((M / 2 : ℕ) : ℤ) % M := hc
      rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at h1
      omega)
    rw [zpow_natCast, zpow_natCast] at h
    exact h
  have hsign : ∑ v ∈ ((Finset.range M).erase (M / 2)).erase 0, (-1 : ℂ) ^ v = -2 := by
    have htot : ∑ v ∈ Finset.range M, (-1 : ℂ) ^ v = 0 := by
      rw [geom_sum_eq (by norm_num) M]
      obtain ⟨k, hk⟩ := hM4
      rw [hk, pow_mul]
      norm_num
    have hM2 : (-1 : ℂ) ^ (M / 2) = 1 := by
      obtain ⟨k, hk⟩ := hM4
      rw [show M / 2 = 2 * k by omega, pow_mul]
      norm_num
    rw [← Finset.add_sum_erase _ _ hhalf, ← Finset.add_sum_erase _ _ hzero, hM2, pow_zero] at htot
    linear_combination htot
  have hsum : ∑ v ∈ Finset.range M, data.character (r ^ v) =
      (Module.finrank ℂ data.vector : ℂ) + ε := by
    rw [← Finset.add_sum_erase _ _ hhalf, ← Finset.add_sum_erase _ _ hzero, ht, pow_zero,
      FiniteComplexRepresentation.character, Representation.char_one]
    rw [Finset.sum_congr rfl hval, ← Finset.mul_sum, hsign]
    ring
  rw [hsum] at hm
  have hM0' : (M : ℂ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have h : (((Module.finrank ℂ data.vector : ℤ) + ε : ℤ) : ℂ) = ((M * m : ℤ) : ℂ) := by
    push_cast
    rw [inv_mul_eq_iff_eq_mul₀ hM0'] at hm
    exact hm
  exact ⟨m, by exact_mod_cast h⟩

theorem card_eq_two_pow_mul_odd {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 3 ≤ n)
    (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* (S : Subgroup G)) (X : Subgroup G)
    (hSX : (S : Subgroup G) ≤ X) : ∃ g : ℕ, Odd g ∧ Nat.card X = 2 ^ n * g := by
  have hS : Nat.card (S : Subgroup G) = 2 ^ n := by
    rw [← Nat.card_congr fS.toEquiv, CFSG.Semidihedral.card n hn]
  have hcard := Subgroup.card_mul_index ((S : Subgroup G).subgroupOf X)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv, hS] at hcard
  refine ⟨((S : Subgroup G).subgroupOf X).index, ?_, hcard.symm⟩
  have hrel := Subgroup.relIndex_mul_index hSX
  have hodd : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
  rcases Nat.even_or_odd ((S : Subgroup G).subgroupOf X).index with h | h
  · exfalso
    apply hodd
    rw [← hrel]
    exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _
  · exact h


theorem cleared_order_formula {cardG c d : ℕ} {A B X Q E : ℚ} (hd : (d : ℚ) ≠ 0) (hX : X ≠ 0)
    (hQ : Q ≠ 0) (h : (cardG : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 * (A * B / X ^ 2) * (E / Q)) :
    (cardG : ℚ) * (d : ℚ) ^ 2 * (X ^ 2 * Q) = (c : ℚ) ^ 3 * (A * B * E) := by
  rw [h]
  field_simp


theorem case_alpha_three_false {G c f ε ℓ γn γd : ℤ} {n : ℕ} (hn : 4 ≤ n)
    (hG : ∃ g : ℤ, Odd g ∧ G = 2 ^ n * g) (hc : ∃ c₀ : ℤ, Odd c₀ ∧ c = 2 ^ n * c₀)
    (hM : (2 : ℤ) ^ (n - 1) ∣ f + ε) (hfodd : Odd f) (hε : ε = 1 ∨ ε = -1) (hℓodd : Odd ℓ)
    (hγ : (γn = 3 ∧ γd = 1) ∨ (γn = 5 ∧ γd = 3))
    (hBr : γd * G * (f + ε) ^ 2 = γn * ℓ * c ^ 2 * (f * (f - ε))) : False := by
  obtain ⟨g, hg, rfl⟩ := hG
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  obtain ⟨k, hk⟩ := hM
  set Y : ℤ := 2 ^ (n - 4) with hYdef
  have hpn : (2 : ℤ) ^ n = 16 * Y := by
    rw [hYdef, ← show (2 : ℤ) ^ 4 = 16 by norm_num, ← pow_add]
    congr 1
    omega
  have hpn1 : (2 : ℤ) ^ (n - 1) = 8 * Y := by
    rw [hYdef, ← show (2 : ℤ) ^ 3 = 8 by norm_num, ← pow_add]
    congr 1
    omega
  have hY0 : Y ≠ 0 := by positivity
  rw [hpn1] at hk
  rw [hpn] at hBr
  have hfe : f - ε = 8 * Y * k - 2 * ε := by linarith
  rw [hk, hfe] at hBr
  have h1 : (512 * Y ^ 2) * (2 * γd * Y * g * k ^ 2) =
      (512 * Y ^ 2) * (γn * ℓ * c₀ ^ 2 * f * (4 * Y * k - ε)) := by
    linear_combination hBr
  have h2 := mul_left_cancel₀ (by positivity : (512 : ℤ) * Y ^ 2 ≠ 0) h1
  have hγodd : Odd γn := by
    rcases hγ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hlast : Odd (4 * Y * k - ε) := by
    rcases hε with rfl | rfl
    · exact ⟨2 * Y * k - 1, by ring⟩
    · exact ⟨2 * Y * k, by ring⟩
  have hodd : Odd (γn * ℓ * c₀ ^ 2 * f * (4 * Y * k - ε)) :=
    ((((hγodd.mul hℓodd).mul (hc₀.pow)).mul hfodd).mul hlast)
  have heven : Even (2 * γd * Y * g * k ^ 2) := ⟨γd * Y * g * k ^ 2, by ring⟩
  rw [h2] at heven
  exact (Int.not_even_iff_odd.mpr hodd) heven

end PrimeTorusExclusion

end CFSG.Semidihedral.Principal
