module

public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeCentralCover
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public noncomputable section

namespace CFSG.RankThree.ReeTitsAut

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.Assembly.RankThreeEven (localRank)

theorem card_mulAut_dvd (T : Type*) [Group T] :
    Nat.card (MulAut T) ∣ Nat.card (Outer T) * Nat.card T := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner T)]
  exact mul_dvd_mul_left _ (Subgroup.card_range_dvd _)


theorem small_Ree_small_rank_core {X : Type*} [Group X] [Finite X] {T : Type} [Group T]
    (Y : Subgroup X) (ℓ f : ℕ) (h : ReeTitsModel T .twistedG2 ℓ f)
    (hX : CFSG.twoLocalOddRank X ≤ 3) (φ : Y →* T) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) :
    ℓ = 3 ∧ f = 3 ∧ ∃ k : ℕ,
      Nat.card (MulAut T) ∣ 3 ^ k * ((3 ^ 3) ^ 3 * (3 ^ 3 - 1) * ((3 ^ 3) ^ 3 + 1)) := by
  obtain ⟨-, -, rfl, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T ℓ f h
  obtain ⟨-, a', hfa', F, _, _, hF, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP F G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hF
  obtain ⟨E⟩ := hiso a' F hfa hF hw
  have hF' : Nat.card F = 3 ^ (2 * a' + 1) := by rw [hF, hfa]
  set ψ : Y →* G2.reeGamma F a' := E.toMonoidHom.comp φ
  have hψ : Function.Surjective ψ := E.surjective.comp hφ
  have hψker : ψ.ker ≤ Subgroup.center Y := fun y hy => hker (by
    rw [MonoidHom.mem_ker] at hy ⊢
    exact E.injective (by simpa [ψ] using hy))
  obtain ⟨⟨-, -, -, V, -, -, hVcard⟩, hrank⟩ :=
    CFSG.RankThree.Chevalley.small_Ree_actual_central_cover_two_local_three_rank Y a' F hF' ψ hψ
      hψker
  have h3X : 3 ∣ Nat.card X := by
    have := Subgroup.card_subgroup_dvd_card V
    rw [hVcard] at this
    exact (dvd_pow_self 3 (by omega)).trans this
  have he := CFSG.RankThree.Theta.localRank_le_twoLocalOddRank Nat.prime_three (by norm_num) h3X
  have ha1 : a' = 1 := by omega
  subst ha1
  refine ⟨rfl, hfa, ?_⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element G2.tag
  obtain ⟨-, -, -, -, -, -, -, -, -, hΓ, -⟩ := small_Ree_Borel_coset_Sylow_action 1 F hF' w₀ hw₀
  obtain ⟨-, -, hFbar, ⟨R, -, -, -, -, hR3, hcompl⟩, -, -⟩ :=
    small_Ree_outer_three_kernel_field_complement 1 le_rfl F hF'
  have : Finite (G2.reeGamma F 1) := Nat.finite_of_card_ne_zero (by rw [hΓ]; norm_num)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR3
  have hout : Nat.card (Outer (G2.reeGamma F 1)) = 3 ^ (k + 1) := by
    rw [← hcompl.card_mul_card, hk, hFbar, pow_succ]
  refine ⟨k + 1, (card_mulAut_dvd T).trans (dvd_of_eq ?_)⟩
  rw [Nat.card_congr (equivalence E).toEquiv, hout, Nat.card_congr E.toEquiv, hΓ]

theorem small_Ree_actual_central_cover_small_rank_no_five_automorphism {J : Type} [Group J]
    [Finite J] (hJ : CFSG.twoLocalOddRank J ≤ 3) (K : Subgroup J) (ℓ f : ℕ)
    (h : ReeTitsModel (K ⧸ Subgroup.center K) .twistedG2 ℓ f) :
    ℓ = 3 ∧ f = 3 ∧ ¬ 5 ∣ Nat.card (MulAut (K ⧸ Subgroup.center K)) ∧
      ∀ α : MulAut (K ⧸ Subgroup.center K), orderOf α ≠ 5 := by
  obtain ⟨hℓ, hf, k, hk⟩ := small_Ree_small_rank_core K ℓ f h hJ
    (QuotientGroup.mk' (Subgroup.center K)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
  have h5 : ¬ 5 ∣ Nat.card (MulAut (K ⧸ Subgroup.center K)) := fun h5 => by
    have h1 := h5.trans hk
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_three).1
        ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h2))
      omega
    · norm_num at h2
  refine ⟨hℓ, hf, h5, fun α hα => h5 ?_⟩
  rw [← hα]
  exact orderOf_dvd_natCard α


end CFSG.RankThree.ReeTitsAut
