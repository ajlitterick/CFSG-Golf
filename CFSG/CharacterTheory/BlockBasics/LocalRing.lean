module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalCoefficientRing
public import CFSG.CharacterTheory.TwoRankLowerBound.LocalizedAlgebraicIntegers

public section

namespace CFSG.BlockBasics

open CFSG CFSG.BrauerThirdMainTheorem.Helpers CFSG.TwoRankLowerBound.Helpers

theorem residue_prime_existence (p : ℕ) (hp : p.Prime) :
    (∃ m : Ideal BlocksAlgInt, m.IsMaximal ∧ (p : BlocksAlgInt) ∈ m) ∧
      ∀ m : Ideal BlocksAlgInt, m.IsMaximal → (p : BlocksAlgInt) ∈ m →
        CharP (BlocksAlgInt ⧸ m) p := by
  refine ⟨?_, ?_⟩
  · have : Algebra.IsIntegral ℤ ComplexAlgebraicIntegers := complexAlgebraicIntegers_integral
    let P : Ideal ℤ := Ideal.span {(p : ℤ)}
    have hPprime : P.IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp)
    have hPbot : P ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    have : P.IsMaximal := hPprime.isMaximal hPbot
    have hker : RingHom.ker (algebraMap ℤ ComplexAlgebraicIntegers) ≤ P := by
      intro z hz
      rw [RingHom.mem_ker] at hz
      have hz' : (z : ℂ) = 0 := by simpa using congrArg Subtype.val hz
      rw [show z = 0 by exact_mod_cast hz']
      exact P.zero_mem
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hker
    refine ⟨Q, hQmax, ?_⟩
    have hpP : (p : ℤ) ∈ P := Ideal.subset_span rfl
    rw [← hQ] at hpP
    simpa using hpP
  · intro m hm hpm
    have : m.IsMaximal := hm
    obtain ⟨q, hq, hchar, hmem⟩ := complexAlgebraicIntegers_maximal_residue_characteristic m
    have hqp : (q : ℤ) ∣ p := (hmem p).mp (by simpa using hpm)
    have hqp' : q ∣ p := by exact_mod_cast hqp
    rcases (Nat.dvd_prime hp).mp hqp' with h | h
    · exact absurd h hq.one_lt.ne'
    · exact h ▸ hchar

theorem localCoefficientSubring_eq_localized (m : Ideal BlocksAlgInt) [hm : m.IsMaximal] :
    localCoefficientSubring m hm = localizedComplexIntegerRing m := by
  ext x
  rw [localizedComplexIntegerRing_mem_iff_fraction]
  change x ∈ BlocksLocalRing m ↔ _
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a, b, hb, rfl⟩
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a, b, hb, rfl⟩

theorem fraction_mem_localMaxIdeal_iff (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (a b : BlocksAlgInt) (hb : b ∉ m) : (a : ℂ) / b ∈ BlocksLocalMaxIdeal m ↔ a ∈ m := by
  constructor
  · rintro ⟨a', b', ha', hb', hequal⟩
    have hb0 := denominator_ne_zero m hb
    have hb'0 := denominator_ne_zero m hb'
    have hcross : (a : ℂ) * b' = a' * b := by
      field_simp at hequal
      linear_combination hequal
    have hcrossInt : a * b' = a' * b := Subtype.ext hcross
    have hmem : a * b' ∈ m := hcrossInt ▸ m.mul_mem_right b ha'
    exact (hm.isPrime.mem_or_mem hmem).resolve_right hb'
  · intro ha
    exact ⟨a, b, ha, hb, rfl⟩


end CFSG.BlockBasics
