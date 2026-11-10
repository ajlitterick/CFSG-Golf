module

public import CFSG.ClassicalInvolution.Asc77.AscC25V13
public import CFSG.ClassicalInvolution.Asc77.AscC25V17

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

section Arith

variable {p : ℕ} [Fact p.Prime]

theorem factorization_sl2 (hp : p ≠ 2) {e₀ f : ℕ} (hf : f = 2 * e₀) (he₀ : 0 < e₀) :
    (Nat.card SL(2, GaloisField p f)).factorization 2 =
      (Nat.card SL(2, GaloisField p e₀)).factorization 2 + 1 := by
  subst hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two (GaloisField p e₀)
  have h2 := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two (GaloisField p (2 * e₀))
  have c1 : Nat.card (GaloisField p e₀) = p ^ e₀ := GaloisField.card p e₀ he₀.ne'
  have c2 : Nat.card (GaloisField p (2 * e₀)) = p ^ (2 * e₀) :=
    GaloisField.card p (2 * e₀) (by omega)
  have hpodd : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp
  have hmodd : Odd (p ^ e₀) := hpodd.pow
  set m := p ^ e₀ with hm
  have hm3 : 3 ≤ m := by
    have h2le : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hp3 : 3 ≤ p := by
      rcases Nat.lt_or_ge p 3 with h | h
      · exfalso
        apply hp
        omega
      · exact h
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e₀ := Nat.pow_le_pow_right (by omega) he₀
  have hmsq : p ^ (2 * e₀) = m * m := by rw [two_mul, pow_add]
  change (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p (2 * e₀)))).factorization 2 =
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p e₀))).factorization 2 + 1
  rw [h1, h2, c1, c2, hmsq]
  have hmm1 : m * m - 1 ≠ 0 := by
    have : 1 < m * m := by nlinarith
    omega
  have hfac : (m * m) ^ 2 - 1 = (m * m - 1) * (m * m + 1) := by
    have : 1 ≤ m * m := by nlinarith
    zify [this, (by nlinarith : 1 ≤ (m * m) ^ 2)]
    ring
  have hm2 : m ^ 2 - 1 = m * m - 1 := by rw [sq]
  rw [hfac, hm2]
  have hm0 : m ≠ 0 := by omega
  have hmm0 : m * m + 1 ≠ 0 := by omega
  have hv : ∀ n : ℕ, n.factorization 2 = padicValNat 2 n := fun n =>
    Nat.factorization_def n Nat.prime_two
  rw [hv, hv, padicValNat.mul (mul_ne_zero hm0 hm0) (mul_ne_zero hmm1 hmm0),
    padicValNat.mul hmm1 hmm0, padicValNat.mul hm0 hm0, padicValNat.mul hm0 hmm1]
  have hv0 : padicValNat 2 m = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro h
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr h))
  have hv1 : padicValNat 2 (m * m + 1) = 1 := by
    obtain ⟨j, hj⟩ := hmodd
    have e : m * m + 1 = 2 * (2 * j * j + 2 * j + 1) := by rw [hj]; ring
    have hodd : Odd (2 * j * j + 2 * j + 1) := ⟨j * j + j, by ring⟩
    have hk : padicValNat 2 (2 * j * j + 2 * j + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by
      intro h
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))
    rw [e, padicValNat.mul (by norm_num) (Nat.succ_ne_zero _), hk]
    simp
  rw [hv0, hv1]
  ring

end Arith

section SylowFixed

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

@[expose] noncomputable def fixHom {K : Subgroup G} {F : Type} [Field F]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) :
    ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) →* ↥(slFix e ⟨a, haN⟩) :=
  ((slProj K e).comp (Subgroup.inclusion inf_le_left)).codRestrict _ fun c => by
    change slAut K e ⟨a, haN⟩ (slProj K e (Subgroup.inclusion inf_le_left c)) =
      slProj K e (Subgroup.inclusion inf_le_left c)
    rw [slAut_slProj]
    congr 1
    apply Subtype.ext
    rw [normalizerConj_apply_coe]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
    change a * c * a⁻¹ = c
    rw [← hc]
    group

theorem fixHom_surjective {K : Subgroup G} {F : Type} [Field F]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) (ha2 : a * a = 1) :
    Function.Surjective (fixHom e haN) := by
  rintro ⟨b, hb⟩
  obtain ⟨c, hca, hcb⟩ := exists_mem_centralizer_of_slAut_eq e haN ha2 hb
  exact ⟨⟨c, c.2, hca⟩, Subtype.ext hcb⟩

theorem mem_oddCoreOf_of_fixHom_eq_one {K : Subgroup G} {F : Type} [Field F]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G))
    {x : ↥(K ⊓ Subgroup.centralizer ({a} : Set G))} (hx : fixHom e haN x = 1) :
    (x : G) ∈ oddCoreOf K := by
  have h2 : slProj K e (Subgroup.inclusion inf_le_left x) = 1 := congrArg Subtype.val hx
  exact (slProj_eq_one_iff e _).mp h2


end SylowFixed

end CFSG.ClassicalInvolution.Asc77.C25V
