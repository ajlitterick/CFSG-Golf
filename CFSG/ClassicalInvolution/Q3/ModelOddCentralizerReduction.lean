module

public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.Q3.OddCentralizerModels
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank


@[expose] def SimpleOddCentralizerFreeTag (t : StatedLieTag) : Prop :=
  ∀ (n : ℕ) (hp : Nat.Prime 3), StatedLieAdmissible t n 3 1 →
    ∀ s : (modelUniv t n 3 1 hp).K ⧸ Subgroup.center (modelUniv t n 3 1 hp).K, orderOf s = 2 →
      CFSG.Assembly.Dichotomy.involutionOddCore s = ⊥


section Central

variable {K X : Type} [Group K] [Group X] (ψ : K →* X) (hψ : Function.Surjective ψ)

include hψ

theorem center_le_map_center_of_perfect [Group.IsPerfect K] (hker : ψ.ker ≤ Subgroup.center K) :
    Subgroup.center X ≤ (Subgroup.center K).map ψ := by
  intro g hg
  obtain ⟨k, rfl⟩ := hψ g
  refine ⟨k, mem_center_of_commutator_mem hker fun h => ?_, rfl⟩
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hg (ψ h)).symm

theorem map_center_le_center : (Subgroup.center K).map ψ ≤ Subgroup.center X := by
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨h, rfl⟩ := hψ g
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hk h]

end Central

section Reduction

variable {X : Type} [Group X] [Finite X]

theorem oddCoreIn_top_eq_bot_of_isQuasisimple (hX : CFSG.Open.IsQuasisimple X)
    (hZ : IsPGroup 2 (Subgroup.center X)) (hinv : ∃ x : X, orderOf x = 2) :
    oddCoreIn (⊤ : Subgroup X) = ⊥ := by
  obtain ⟨x, hx⟩ := hinv
  set S := oddCoreIn (⊤ : Subgroup X) with hS
  have hSodd : Odd (Nat.card S) := odd_card_oddCoreIn _
  have hSn : S.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (normalizer_oddCoreIn ⊤))
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hX S with hc | htop
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := hZ ⟨g, hc hg⟩
    have h1 : g ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have h3 : Odd (orderOf g) :=
      Odd.of_dvd_nat hSodd (Subgroup.orderOf_dvd_natCard _ hg)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      ((Nat.coprime_two_right.mpr h3).pow_right k) h2)
  · exfalso
    have hodd : Odd (Nat.card (⊤ : Subgroup X)) := htop ▸ hSodd
    rw [Subgroup.card_top] at hodd
    have h2 : 2 ∣ Nat.card X := hx ▸ orderOf_dvd_natCard x
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end Reduction


end CFSG.ClassicalInvolution.Q3
