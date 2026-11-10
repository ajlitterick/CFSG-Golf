module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.RankThree.PartOne.K133H.F4Torus

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.Timmesfeld.ExceptionalOrders CFSG.Open

theorem factorization_ordF4_of_dvd_add_one {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hd : p ∣ q + 1) : (ordF4 q).factorization p = 4 * (q + 1).factorization p := by
  have hp2 : p ≠ 2 := by omega
  have hpq : ¬ p ∣ q := by
    intro h
    have h1 : p ∣ (q + 1) - q := Nat.dvd_sub hd h
    rw [show q + 1 - q = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpq1 : ¬ p ∣ q - 1 := by
    intro h
    have h1 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hd h
    rw [show q + 1 - (q - 1) = 2 by omega] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hQ : 2 ≤ q ^ 2 := le_trans hq (Nat.le_self_pow (by norm_num) q)
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rcases q with _ | q
    · omega
    · simp only [Nat.add_sub_cancel]
      ring_nf
      omega
  have hdQ : p ∣ q ^ 2 - 1 := hsq ▸ dvd_mul_of_dvd_right hd _
  have hsq0 : (q ^ 2 - 1).factorization p = (q + 1).factorization p := by
    rw [hsq, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpq1, zero_add]
  have hnd : ∀ k : ℕ, k = 3 ∨ k = 4 ∨ k = 6 → ¬ p ∣ k := by
    intro k hk h
    have hle : p ≤ k := Nat.le_of_dvd (by omega) h
    have hk6 : p ≤ 6 := by omega
    interval_cases p <;> rcases hk with rfl | rfl | rfl <;> first | omega | (norm_num at hp)
  have hpow : ∀ k : ℕ, k = 3 ∨ k = 4 ∨ k = 6 →
      ((q ^ 2) ^ k - 1).factorization p = (q + 1).factorization p := fun k hk => by
    rw [CFSG.RankThree.PartOne.K133H.factorization_pow_sub_one hp hp2 hQ hdQ (by omega)
      (hnd k hk), hsq0]
  have h12 : q ^ 12 - 1 = (q ^ 2) ^ 6 - 1 := by rw [← pow_mul]
  have h8 : q ^ 8 - 1 = (q ^ 2) ^ 4 - 1 := by rw [← pow_mul]
  have h6 : q ^ 6 - 1 = (q ^ 2) ^ 3 - 1 := by rw [← pow_mul]
  have hne : ∀ k, k ≠ 0 → q ^ k - 1 ≠ 0 := fun k hk =>
    Nat.sub_ne_zero_of_lt (lt_of_lt_of_le (by omega : 1 < q) (Nat.le_self_pow hk q))
  have hq24 : q ^ 24 ≠ 0 := by positivity
  have e12 := hne 12 (by norm_num)
  have e8 := hne 8 (by norm_num)
  have e6 := hne 6 (by norm_num)
  have e2 := hne 2 (by norm_num)
  unfold ordF4
  rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hq24 e12) e8) e6) e2,
    Nat.factorization_mul (mul_ne_zero (mul_ne_zero hq24 e12) e8) e6,
    Nat.factorization_mul (mul_ne_zero hq24 e12) e8, Nat.factorization_mul hq24 e12]
  simp only [Finsupp.add_apply]
  rw [h12, h8, h6, hpow 6 (by omega), hpow 4 (by omega), hpow 3 (by omega), hsq0,
    Nat.factorization_eq_zero_of_not_dvd (fun h => hpq (hp.dvd_of_dvd_pow h))]
  ring

section Model

variable (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]


noncomputable def twModelEquivF4 {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.F4 L} (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.F4) L f4Neg) :
    adjointGroup Tag.F4 K ≃* twModel (canonicalRep (coxeterSystem Tag.F4) L f4Neg) Fr :=
  ((adjointGroup Tag.F4 K).equivMapOfInjective _ (baseChangeGL_injective _)).trans
    ((MulEquiv.subgroupCongr ((map_conj_twModel hg0C hg0).trans
      (G2_F4_exact_finite_field_fixed_root_matrices Tag.F4 (Or.inr rfl) K L Fr hFr).1)).symm.trans
      ((MulAut.conj g0).subgroupMap _).symm)

theorem finite_twModelF4 {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.F4 L} (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.F4) L f4Neg) :
    Finite (twModel (canonicalRep (coxeterSystem Tag.F4) L f4Neg) Fr) := by
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  exact Finite.of_equiv _ (twModelEquivF4 K L hFr hg0C hg0).toEquiv


end Model

end CFSG.HardMathSupport.Timmesfeld.CrossChar
