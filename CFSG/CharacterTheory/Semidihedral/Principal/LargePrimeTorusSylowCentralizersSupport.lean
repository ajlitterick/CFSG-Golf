module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionPrincipalColumnSum
public import CFSG.CharacterTheory.Semidihedral.Principal.SignedDegreeNumerics
public import CFSG.CharacterTheory.Semidihedral.Principal.RealOddPrincipalBlock
public import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2FixedPointBound
public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneTorusNormalizer

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

namespace LargePrimeTorus

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.GorensteinWalter


theorem nonempty_equiv_alternating_five_of_model {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 5 1) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨iso⟩⟩ := h
  obtain ⟨⟨e5⟩, -⟩ := CFSG.LinearGroups.five_field_linear_two_alternating_five_model F
    (by rw [hcard]; norm_num)
  exact ⟨iso.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans e5)⟩


theorem column_bracket_eq {F x δ : ℂ} (hδ : δ = 1 ∨ δ = -1) (hF : F ≠ 0) (hFδ : F + δ ≠ 0) :
    1 + δ * x ^ 2 / F - δ * (x + δ) ^ 2 / (F + δ) = (F - x) ^ 2 / (F * (F + δ)) := by
  field_simp
  rcases hδ with rfl | rfl <;> ring


theorem order_column_cancel {Gc c d X Y Y' Z A m q : ℚ} (hX : X ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hq : q ≠ 0) (hG : Gc = c ^ 3 / d ^ 2 * (Y / X ^ 2) * (Z / q))
    (h3 : 3 * Gc * X ^ 2 = A * m * c ^ 2 * Y') :
    3 * c * Y * Z = A * m * d ^ 2 * q * Y' := by
  subst hG
  have h : c ^ 2 * (3 * c * Y * Z - A * m * d ^ 2 * q * Y') = 0 := by
    have h' : 3 * (c ^ 3 / d ^ 2 * (Y / X ^ 2) * (Z / q)) * X ^ 2 * (d ^ 2 * q) =
        A * m * c ^ 2 * Y' * (d ^ 2 * q) := by rw [h3]
    have hl : 3 * (c ^ 3 / d ^ 2 * (Y / X ^ 2) * (Z / q)) * X ^ 2 * (d ^ 2 * q) =
        3 * c ^ 3 * Y * Z := by
      field_simp
    rw [hl] at h'
    linear_combination h'
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0) hc
  · linarith

theorem order_column_int {Gc c m : ℕ} {X Y Y' Z A q e : ℤ} (hX : X ≠ 0) (hc : c ≠ 0) (hm : m ≠ 0)
    (hq : q ≠ 0)
    (hG : (Gc : ℚ) = (c : ℚ) ^ 3 / ((4 * m : ℕ) : ℚ) ^ 2 * ((Y : ℚ) / (X : ℚ) ^ 2) * ((Z : ℚ) / q))
    (h3 : 3 * (Gc : ℤ) * X ^ 2 = A * m * (c : ℤ) ^ 2 * Y') (hm2 : 2 * (m : ℤ) = q + e) :
    3 * (c : ℤ) * Y * Z = A * m * (2 * (q + e)) ^ 2 * q * Y' := by
  have h3Q : 3 * (Gc : ℚ) * (X : ℚ) ^ 2 = (A : ℚ) * (m : ℚ) * (c : ℚ) ^ 2 * (Y' : ℚ) := by
    exact_mod_cast h3
  have h := order_column_cancel (Int.cast_ne_zero.mpr hX) (Nat.cast_ne_zero.mpr hc)
    (Nat.cast_ne_zero.mpr (by omega : 4 * m ≠ 0)) (Int.cast_ne_zero.mpr hq) hG h3Q
  have h' : 3 * (c : ℤ) * Y * Z = A * m * ((4 * m : ℕ) : ℤ) ^ 2 * q * Y' := by exact_mod_cast h
  rw [h']
  push_cast
  rw [show (4 : ℤ) * m = 2 * (2 * m) by ring, hm2]

theorem chi_two_false {q e A Y m : ℤ} (he : e = 1 ∨ e = -1) (hA : A = 9 ∨ A = 5) (hq : 9 ≤ q)
    (hY : Y ≠ 0) (hm : 2 * m = q + e)
    (h : 3 * (2 * q * (q ^ 2 - 1)) * Y * (q - e) = A * m * (2 * (q + e)) ^ 2 * q * Y) :
    False := by
  have hqe : 0 < q + e := by rcases he with rfl | rfl <;> omega
  have h' : 2 * q * Y * (q + e) * (3 * (q - e) ^ 2 - A * (q + e) ^ 2) = 0 := by
    rcases he with rfl | rfl
    · linear_combination h + 2 * A * q * Y * (q + 1) ^ 2 * hm
    · linear_combination h + 2 * A * q * Y * (q + -1) ^ 2 * hm
  have hne : 2 * q * Y * (q + e) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by omega) hY) (by omega)
  have h0 := (mul_eq_zero.mp h').resolve_left hne
  rcases he with rfl | rfl <;> rcases hA with rfl | rfl <;> nlinarith

theorem chi_one_four_false {q e δ f m : ℤ} (he : e = 1 ∨ e = -1) (hδ : δ = 1 ∨ δ = -1)
    (hq : 9 ≤ q) (hf : 1 < f) (hfodd : Odd f) (hm : 2 * m = q + e)
    (h : 3 * (2 * q * (q ^ 2 - 1)) * (f * (f + δ)) * (q + e) =
      9 * m * (2 * (q + e)) ^ 2 * q * (f * (f - δ))) : False := by
  have hf3 : 3 ≤ f := by
    obtain ⟨k, hk⟩ := hfodd
    omega
  have hqe : 0 < q + e := by rcases he with rfl | rfl <;> omega
  have h' : 6 * q * f * (q + e) ^ 2 * ((q - e) * (f + δ) - 3 * (q + e) * (f - δ)) = 0 := by
    rcases he with rfl | rfl
    · linear_combination h + 18 * q * f * (q + 1) ^ 2 * (f - δ) * hm
    · linear_combination h + 18 * q * f * (q + -1) ^ 2 * (f - δ) * hm
  have hne : 6 * q * f * (q + e) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by omega) (by omega)) (pow_ne_zero _ (by omega))
  have h0 := (mul_eq_zero.mp h').resolve_left hne
  rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> nlinarith

theorem chi_one_five_false {q e δ f m : ℤ} (he : e = 1 ∨ e = -1) (hδ : δ = 1 ∨ δ = -1)
    (hm7 : 7 ≤ m) (hm9 : m ≠ 9) (hf : 1 < f) (hm : 2 * m = q + e)
    (h : 3 * (2 * q * (q ^ 2 - 1)) * (f * (f + δ)) * (q + e) =
      5 * m * (2 * (q + e)) ^ 2 * q * (f * (f - δ))) : False := by
  have hq : 13 ≤ q := by rcases he with rfl | rfl <;> omega
  have hqe : 0 < q + e := by rcases he with rfl | rfl <;> omega
  have h' : 2 * q * f * (q + e) ^ 2 * (3 * (q - e) * (f + δ) - 5 * (q + e) * (f - δ)) = 0 := by
    rcases he with rfl | rfl
    · linear_combination h + 10 * q * f * (q + 1) ^ 2 * (f - δ) * hm
    · linear_combination h + 10 * q * f * (q + -1) ^ 2 * (f - δ) * hm
  have hne : 2 * q * f * (q + e) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by omega) (by omega)) (pow_ne_zero _ (by omega))
  have h0 := (mul_eq_zero.mp h').resolve_left hne
  have hkey : (q + 4 * e) * (f - 4 * δ) = -15 * e * δ := by
    have h2 : 2 * ((q + 4 * e) * (f - 4 * δ) + 15 * e * δ) = 0 := by
      rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> linear_combination -h0
    linarith
  set u := f - 4 * δ with hu
  rcases lt_trichotomy u 0 with hu0 | hu0 | hu0
  · rcases le_or_gt u (-2) with hu2 | hu2
    · rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> nlinarith
    · have hu1 : u = -1 := by omega
      rw [hu1] at hkey
      rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> omega
  · rw [hu0] at hkey
    rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> omega
  · rcases le_or_gt 2 u with hu2 | hu2
    · rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> nlinarith
    · have hu1 : u = 1 := by omega
      rw [hu1] at hkey
      rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> omega

theorem chi_three_false {g c' A m f δ y : ℤ} {n : ℕ} (hn : 4 ≤ n) (hδ : δ = 1 ∨ δ = -1)
    (hA : Odd A) (hm : Odd m) (hc' : Odd c') (hf : Odd f) (hy : f + δ = 2 ^ (n - 1) * y)
    (h : 3 * (2 ^ n * g) * (f + δ) ^ 2 = A * m * (2 ^ n * c') ^ 2 * f * (f - δ)) : False := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h1 : (2 : ℤ) ^ (k + 4 - 1) = 8 * 2 ^ k := by
    rw [show k + 4 - 1 = k + 3 by omega, pow_add]
    ring
  rw [h1] at hy
  have hfd : f - δ = 2 * (4 * 2 ^ k * y - δ) := by linear_combination hy
  rw [hy, hfd] at h
  have h' : (2 : ℤ) ^ k * 2 ^ k * 512 * (6 * 2 ^ k * g * y ^ 2 -
      A * m * c' ^ 2 * f * (4 * 2 ^ k * y - δ)) = 0 := by
    linear_combination h
  have hne : (2 : ℤ) ^ k * 2 ^ k * 512 ≠ 0 := by positivity
  have h0 := (mul_eq_zero.mp h').resolve_left hne
  have hodd : Odd (A * m * c' ^ 2 * f * (4 * 2 ^ k * y - δ)) := by
    have hodd' : Odd (4 * 2 ^ k * y - δ) := by
      rcases hδ with rfl | rfl
      · exact ⟨2 * 2 ^ k * y - 1, by ring⟩
      · exact ⟨2 * 2 ^ k * y, by ring⟩
    exact (((hA.mul hm).mul (hc'.pow)).mul hf).mul hodd'
  have heven : Even (6 * 2 ^ k * g * y ^ 2) := ⟨3 * 2 ^ k * g * y ^ 2, by ring⟩
  rw [sub_eq_zero] at h0
  rw [h0] at heven
  exact (Int.not_even_iff_odd.mpr hodd) heven


open CFSG.TwoRankLowerBound.Helpers in
theorem characterPairing_column_eq {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (ρ τ : basis.index) (δ : ℂ)
    (T : G → ℂ) (hT : ∀ g, T g = 1 + δ * (basis.representation ρ).character g -
      δ * (basis.representation τ).character g) (α : basis.index) :
    characterPairing T (basis.representation α).character =
      (if principal = α then 1 else 0) + δ * (if ρ = α then 1 else 0) -
        δ * (if τ = α then 1 else 0) := by
  have hsplit : characterPairing T (basis.representation α).character =
      characterPairing (basis.representation principal).character
          (basis.representation α).character +
        δ * characterPairing (basis.representation ρ).character
          (basis.representation α).character -
        δ * characterPairing (basis.representation τ).character
          (basis.representation α).character := by
    unfold characterPairing
    rw [hprincipal]
    simp only [hT, Pi.one_apply, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  rw [hsplit]
  simp_rw [characterPairing_irreducible _ _ (basis.irreducible _) (basis.irreducible α),
    basis.distinct.eq_iff]

theorem sum_column_coefficients {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c : ι) (δ : ℂ)
    (g : ι → ℂ) :
    ∑ α, ((if a = α then 1 else 0) + δ * (if b = α then 1 else 0) -
      δ * (if c = α then 1 else 0)) * g α = g a + δ * g b - δ * g c := by
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc,
    ← Finset.mul_sum, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]


end LargePrimeTorus

namespace LargePrimeTorus

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  CFSG.LyonsUnitaryFour


end LargePrimeTorus

end CFSG.Semidihedral.Principal
