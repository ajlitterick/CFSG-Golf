module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC
public import CFSG.ClassicalInvolution.Balance.Q27D4Parts

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Balance.Q27

variable {p : ℕ} [Fact p.Prime]

section Existence

theorem exists_short_fund_trialityD4 (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 0 p e) :
    ∃ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e Fact.out).D,
      ⁅R, R⁆ = R ∧ ∃ c, IsUniqueInvolution R c := by
  have he : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    hK (fun c => iterateFrobenius_def p e c)
  have hodd : Odd (Nat.card (GaloisField p (3 * e))) := by
    rw [GaloisField.card p (3 * e) (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have h4S : 4 ≤ Nat.card (GaloisField p (3 * e)) := by
    rw [hK]
    exact four_le_pow_three (by
      calc 2 ≤ 3 := by norm_num
        _ ≤ p := hp3
        _ ≤ p ^ e := Nat.le_self_pow (by omega) p)
  set i : Fin (modelUniv .trialityD4 0 p e Fact.out).D.rank :=
    ⟨1, by show 1 < 2; exact Nat.one_lt_two⟩ with hi
  have hR : rankOne (modelUniv .trialityD4 0 p e Fact.out).D.rootGroup i =
      (slShort (iterateFrobenius (GaloisField p (3 * e)) p e) hσ).range :=
    ModelFacts.rankOne_short_eq_range hσ
  refine ⟨(slShort (iterateFrobenius (GaloisField p (3 * e)) p e) hσ).range, ?_, ?_, ?_⟩
  · rw [← hR]
    exact ⟨1, Pi.single i 1, Or.inr (Or.inr ⟨rfl,
      CFSG.ClassicalInvolution.Balance.single_mem_roots _ i⟩), (conjSub_one _).symm⟩
  · refine le_antisymm (Subgroup.commutator_le.mpr fun x hx y hy => ?_) ?_
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
        (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    · have h1 := ModelFacts.fundPerfect_range_le_commutator
        (CFSG.ClassicalInvolution.sl2_isPerfect h4S)
        (slShort (iterateFrobenius (GaloisField p (3 * e)) p e) hσ)
      exact h1
  · exact ⟨_, isUniqueInvolution_range_sl2 hodd
      (slShort_injective hσ)⟩

theorem exists_perfect_fund_of_involution (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 0 p e)
    {u : (modelUniv .trialityD4 0 p e Fact.out).K} (hu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e Fact.out).D,
      ⁅R, R⁆ = R ∧ IsUniqueInvolution R u := by
  obtain ⟨R₀, hR₀, hperf, c₀, hc₀⟩ := exists_short_fund_trialityD4 hp2 hadm
  obtain ⟨g, hg⟩ : ∃ g : (modelUniv .trialityD4 0 p e Fact.out).K, g * c₀ * g⁻¹ = u :=
    Balance.Bootstrap.trialityD4_involutions_conj hp2 hadm.2.1
      (x := c₀) (x' := u) hc₀.sq hu hc₀.ne_one hu1
  refine ⟨conjSub g R₀, RouteD.conjSub_mem_fundamentalSubgroups hR₀ g, ?_, ?_⟩
  · show ⁅R₀.map (MulAut.conj g).toMonoidHom, R₀.map (MulAut.conj g).toMonoidHom⁆ =
      R₀.map (MulAut.conj g).toMonoidHom
    rw [← Subgroup.map_commutator, hperf]
  · have := hc₀.conj g
    rwa [hg] at this

end Existence

section Centralizers


end Centralizers

section D4Three

@[expose] def TD4ThreeOddCore : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), StatedLieAdmissible .trialityD4 n p e → p ^ e = 3 →
    InvolutionOddCoreTrivial (modelUniv .trialityD4 n p e hp).K


end D4Three

end CFSG.ClassicalInvolution.G2D4Models
