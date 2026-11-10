module

public import CFSG.ClassicalInvolution.Asc77.AscC25V16
public import CFSG.ClassicalInvolution.Asc77.AscC25V18
public import CFSG.ClassicalInvolution.Asc77.AscC25V20

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_comm_order_four_of_commute (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {a b : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) (hbN : b ∈ Subgroup.normalizer (K : Set G))
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (hσa : fieldChar hp hq e ⟨a, haN⟩ ≠ 1) (hσb : fieldChar hp hq e ⟨b, hbN⟩ = 1) :
    ∃ y₀ ∈ K, orderOf y₀ = 4 ∧ y₀ * b = b * y₀ := by
  obtain ⟨hf, hcard, hoddp, h3⟩ := gf_facts hp hq
  set na : Subgroup.normalizer (K : Set G) := ⟨a, haN⟩ with hna
  set nb : Subgroup.normalizer (K : Set G) := ⟨b, hbN⟩ with hnb
  have hna2 : na * na = 1 := Subtype.ext ha2
  have hnb2 : nb * nb = 1 := Subtype.ext hb2
  set σ := fieldChar hp hq e na with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul, hna2, map_one]
  have hσ2' : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : GaloisField p f ≃+* GaloisField p f => τ x) hσ2
    simpa using this
  obtain ⟨k, hfk, hσk⟩ := eq_frobenius_of_sq_eq_one hf hσ2 hσa
  obtain ⟨A, hA⟩ := exists_semilinHom_of_mem e hcard hoddp h3 na
  obtain ⟨B, hB⟩ := exists_semilinHom_of_mem e hcard hoddp h3 nb
  have hA' : ∀ x, slAut K e na x = semilinHom A σ x := hA
  have hB' : ∀ x, slAut K e nb x = semilinHom B 1 x := by
    intro x
    rw [hB x]
    have : (normalizerToPGammaL2Mod e hcard hoddp h3 nb).right = 1 := hσb
    rw [this]
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hfk
    exact hf hfk
  have hp2' : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp3 : 3 ≤ p := by
    rcases Nat.lt_or_ge p 3 with h | h
    · exfalso
      apply hp
      omega
    · exact h
  have hm3 : 3 ≤ p ^ k := hp3.trans (Nat.le_self_pow hk0 p)
  have hmodd : Odd (p ^ k) := ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  have hF : Nat.card (GaloisField p f) = (p ^ k) ^ 2 := by
    rw [hcard, hfk, ← pow_mul, mul_comm]
  have h2F : (2 : GaloisField p f) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p f) p]; exact hp)
  have hAA : ∀ x, semilinHom A σ (semilinHom A σ x) = x := by
    intro x
    have := slAut_slAut_of_mul_self e na ha2 x
    rwa [hA', hA'] at this
  have hBB : ∀ x, semilinHom B 1 (semilinHom B 1 x) = x := by
    intro x
    have := slAut_slAut_of_mul_self e nb hb2 x
    rwa [hB', hB'] at this
  have hnab : na * nb = nb * na := Subtype.ext hab
  have hAB : ∀ x, semilinHom A σ (semilinHom B 1 x) = semilinHom B 1 (semilinHom A σ x) := by
    intro x
    have h1 : slAut K e na (slAut K e nb x) = slAut K e nb (slAut K e na x) := by
      have h2 : slAut K e (na * nb) x = slAut K e (nb * na) x := by rw [hnab]
      simpa [slAut] using h2
    rwa [hA', hB', hB', hA'] at h1
  obtain ⟨y, hy4, hyfix⟩ := exists_fixed_order_four hF hm3 hmodd h2F σ hσk hσ2' A B hAA hBB hAB
  have hyfix' : slAut K e nb y = y := by rw [hB']; exact hyfix
  obtain ⟨c, hcC, hcy⟩ := exists_mem_centralizer_of_slAut_eq e hbN hb2 hyfix'
  have hc4 : 4 ∣ orderOf c := by
    have h1 : orderOf (slProj K e c) ∣ orderOf c := orderOf_map_dvd (slProj K e) c
    rwa [hcy, hy4] at h1
  have hcne : orderOf c ≠ 0 := (orderOf_pos c).ne'
  refine ⟨((c ^ (orderOf c / 4) : K) : G), (c ^ (orderOf c / 4)).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div hcne hc4
  · have hcb : (c : G) * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
    have : ((c ^ (orderOf c / 4) : K) : G) = (c : G) ^ (orderOf c / 4) := rfl
    rw [this]
    exact (Commute.pow_left (show Commute (c : G) b from hcb) _).eq

end Group

section Hyp


end Hyp

end CFSG.ClassicalInvolution.Asc77.C25V
