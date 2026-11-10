module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKInputs
import CFSG.Quasithin.H13.A7SectionRank
import CFSG.GroupTheory.PRankBound
public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup


theorem s16k_u43_noncyclic3 (hT : S16kU43Noncyclic3) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    (hS : ∃ S : Type, ∃ _ : Group S, CFSG.Blueprint.LieModel S .PSU 4 3 1 ∧ IsHat ↥H S)
    (hrk : rk ↥(⊤ : Subgroup W) = 12) (hirr : IsIrrOn H ⊤ ⊥) :
    ∀ w : W, w ≠ 1 → ∃ B : Subgroup (MulAut W), B ≤ H ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
      ∀ b ∈ B, b w = w :=
  hT W hW H hS hrk hirr

private theorem s16k_finite_of_lieModel_u43 {S : Type} [Group S]
    (h : CFSG.Blueprint.LieModel S .PSU 4 3 1) : Finite S := by
  obtain ⟨-, K, hKfield, hKfinite, -, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  exact Finite.of_injective e.toEquiv e.toEquiv.injective

private theorem s16k_card_outer_u43 {S : Type} [Group S]
    (h : CFSG.Blueprint.LieModel S .PSU 4 3 1) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 2 ^ 3 := by
  have hcl : StatedClassicalModel S .PSU 4 3 1 := h.statedClassicalModel (by decide)
  have hcard :=
    (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound S 4 3 1 hcl).2.2.1
  norm_num at hcard
  rw [hcard]
  norm_num

private theorem s16k_card_mulAut_dvd {S : Type} [Group S] [Finite S]
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 2 ^ 3) :
    Nat.card (MulAut S) ∣ Nat.card S * 2 ^ 3 := by
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) ∣
      Nat.card S := by
    unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
    exact Subgroup.card_range_dvd _
  rw [← Subgroup.card_mul_index
    (CFSG.ComponentClassification.OuterAutomorphisms.inner S), Subgroup.index_eq_card]
  exact mul_dvd_mul hinner hout

private theorem s16k_not_dvd_sq_u43 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ (2 ^ 7 * 3 ^ 6 * 5 * 7) * 2 ^ 3 := by
  have heq : (2 ^ 7 * 3 ^ 6 * 5 * 7) * 2 ^ 3 = 2 ^ 10 * 3 ^ 6 * 5 * 7 := by norm_num
  rw [heq]
  intro h
  have hpdvd : p ∣ 2 ^ 10 * 3 ^ 6 * 5 * 7 := (dvd_pow_self p (by norm_num)).trans h
  rcases (Nat.Prime.dvd_mul hp).1 hpdvd with h1 | h7
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h23 | h5
    · rcases (Nat.Prime.dvd_mul hp).1 h23 with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
    · have hp5' : p = 5 := le_antisymm (Nat.le_of_dvd (by norm_num) h5) hp5
      subst hp5'
      norm_num at h
  · have hp7 : p ≤ 7 := Nat.le_of_dvd (by norm_num) h7
    rcases (by omega : p = 5 ∨ p = 6 ∨ p = 7) with rfl | rfl | rfl
    · norm_num at h
    · norm_num at hp
    · norm_num at h

theorem s16k_pRank_aut_u43 {X : Type} [Group X] [Finite X] {S : Type} [Group S]
    (hS : CFSG.Blueprint.LieModel S .PSU 4 3 1) (hX : IsHat X S) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) : CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 1 := by
  haveI : Finite S := s16k_finite_of_lieModel_u43 hS
  obtain ⟨hquasi, -, ⟨e⟩⟩ := hX
  haveI : Group.IsPerfect X := hquasi.1
  have hinj : Function.Injective
      ((MulAut.congr e).toMonoidHom.comp
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X)) :=
    (MulAut.congr e).injective.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective X)
  refine (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt _ hinj).trans ?_
  have hcardS : Nat.card S = 2 ^ 7 * 3 ^ 6 * 5 * 7 := by
    rw [CFSG.GH74.card_of_lieModel_PSU (n := 4) (p := 3) (f := 1)
      (by norm_num) (by norm_num) hS]
    decide
  have hnot : ¬ p ^ (1 + 1) ∣ Nat.card (⊤ : Subgroup (MulAut S)) := by
    rw [Subgroup.card_top]
    intro hdiv
    refine s16k_not_dvd_sq_u43 hp hp5 (hcardS ▸ ?_)
    exact hdiv.trans (s16k_card_mulAut_dvd (s16k_card_outer_u43 hS))
  exact CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hp hnot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
