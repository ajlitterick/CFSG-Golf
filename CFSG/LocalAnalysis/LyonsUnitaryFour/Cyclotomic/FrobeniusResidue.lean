module

public import CFSG.CharacterTheory.TwoRankLowerBound.AlgebraicIntegerResidue
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers IntermediateField Polynomial

theorem exists_frobenius_exponent {p a M : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    ∃ k : ℕ, k.Coprime (p ^ a * M) ∧ k ≡ 1 [MOD p ^ a] ∧ k ≡ p [MOD M] := by
  have hcop : (p ^ a).Coprime M :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)
  let k := Nat.chineseRemainder hcop 1 p
  have h1 : (k : ℕ) ≡ 1 [MOD p ^ a] := k.2.1
  have h2 : (k : ℕ) ≡ p [MOD M] := k.2.2
  refine ⟨k, ?_, h1, h2⟩
  apply Nat.Coprime.mul_right
  · rw [Nat.Coprime, h1.gcd_eq, Nat.gcd_one_left]
  · rw [Nat.Coprime, h2.gcd_eq]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM

theorem isCyclotomicExtension_adjoin_primitiveRoot {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := by
  have hζalg : IsAlgebraic ℚ ζ := by
    refine ⟨cyclotomic N ℚ, cyclotomic_ne_zero N ℚ, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff]
    exact hζ
  change IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯.toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg]
  exact hζ.adjoin_isCyclotomicExtension ℚ

theorem isPrimitiveRoot_adjoinSimple_gen {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    IsPrimitiveRoot (AdjoinSimple.gen ℚ ζ) N :=
  IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ

theorem exists_galois_gen_eq_pow {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {k : ℕ}
    (hk : k.Coprime N) :
    ∃ σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯, σ (AdjoinSimple.gen ℚ ζ) = AdjoinSimple.gen ℚ ζ ^ k := by
  have : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := isCyclotomicExtension_adjoin_primitiveRoot hζ
  have : NumberField ℚ⟮ζ⟯ := IsCyclotomicExtension.numberField {N} ℚ ℚ⟮ζ⟯
  let σ := (IsCyclotomicExtension.Rat.galEquivZMod N ℚ⟮ζ⟯).symm (ZMod.unitOfCoprime k hk)
  refine ⟨σ, ?_⟩
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N ℚ⟮ζ⟯ σ
    (isPrimitiveRoot_adjoinSimple_gen hζ).pow_eq_one]
  simp only [σ, MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime]
  rw [ZMod.val_natCast, (isPrimitiveRoot_adjoinSimple_gen hζ).eq_orderOf, pow_mod_orderOf]


theorem pow_eq_pow_of_modEq {R : Type*} [Monoid R] {w : R} {M k l : ℕ} (hw : w ^ M = 1)
    (h : k ≡ l [MOD M]) : w ^ k = w ^ l := by
  rw [← Nat.mod_add_div k M, ← Nat.mod_add_div l M, pow_add, pow_add, pow_mul, pow_mul, hw,
    one_pow, one_pow, show k % M = l % M from h]


section Frobenius

variable {p a M N k : ℕ} {ζ : ℂ}

theorem galois_gen_eq_pow_of_coe {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯}
    (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) :
    σ (AdjoinSimple.gen ℚ ζ) = AdjoinSimple.gen ℚ ζ ^ k :=
  Subtype.ext (by simpa using hσ)

theorem galois_apply_of_pow_eq_one [NeZero N] (hζ : IsPrimitiveRoot ζ N)
    {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯} (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) {ξ : ℚ⟮ζ⟯}
    (hξ : ξ ^ N = 1) : σ ξ = ξ ^ k := by
  obtain ⟨i, -, rfl⟩ := (isPrimitiveRoot_adjoinSimple_gen hζ).eq_pow_of_pow_eq_one hξ
  rw [map_pow, galois_gen_eq_pow_of_coe hσ, ← pow_mul, ← pow_mul, mul_comm]

theorem cyclotomic_frobenius_exists (hp : p.Prime) (hN : N = p ^ a * M) (hpM : ¬ p ∣ M)
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ N) :
    ∃ k : ℕ, k.Coprime N ∧ k ≡ 1 [MOD p ^ a] ∧ k ≡ p [MOD M] ∧
      ∃ σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯, (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k := by
  have : NeZero N := ⟨by rw [hN]; exact (Nat.mul_pos (pow_pos hp.pos a) hM).ne'⟩
  obtain ⟨k, hk, hk1, hkp⟩ := exists_frobenius_exponent (a := a) hp hpM
  rw [← hN] at hk
  obtain ⟨σ, hσ⟩ := exists_galois_gen_eq_pow hζ hk
  exact ⟨k, hk, hk1, hkp, σ, by rw [hσ]; simp⟩


end Frobenius

end CFSG.LyonsUnitaryFour
