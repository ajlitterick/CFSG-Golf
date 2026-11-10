module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeK1
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07

variable {G : Type} [Group G] [Finite G]

theorem uc22s13xo_three_dvd_sub_one {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  have h : 2 ^ n % 3 = 1 := by
    obtain ⟨j, rfl⟩ := hn
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  omega

theorem uc22s13xo_center_pRank {L : Subgroup G} {n : ℕ} (hn : IsPowTwo n)
    (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) :
    center (Bar2 L) = ⊥ ∧ CFSG.Open.pRank 3 L = 1 := by
  refine ⟨(uc22s13xg_even_center_outer hn hX).2.1, ?_⟩
  rcases hX with h | h
  · exact PartTwo.S17.pRank_three_eq_one_of_isL2 h
  · exact PartTwo.S17.pRank_three_eq_one_of_isU3FourPow h hn (PartTwo.s13_two_le_of_isU3 h)

theorem uc22s13xo_three_dvd_card {L : Subgroup G} (h : CFSG.Open.pRank 3 L = 1) :
    3 ∣ Nat.card L := by
  obtain ⟨E, hEL, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) L
  rw [h, pow_one] at hE
  rw [← hE]
  exact Subgroup.card_dvd_of_le hEL

theorem uc22s13xo_hyp81 {M L₁ L₂ L₃ : Subgroup G} (h₁ : L₁ ∈ calC M) (h₂ : L₂ ∈ calC M)
    (h₃ : L₃ ∈ calC M) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃)
    (s₁ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₁) n ∨ IsU3 (Bar2 L₁) n))
    (s₂ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₂) n ∨ IsU3 (Bar2 L₂) n))
    (s₃ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₃) n ∨ IsU3 (Bar2 L₃) n)) :
    F08.Hyp81 M (L₁ ⊔ L₂ ⊔ L₃) := by
  classical
  obtain ⟨n₁, hn₁, hX₁⟩ := s₁
  obtain ⟨n₂, hn₂, hX₂⟩ := s₂
  obtain ⟨n₃, hn₃, hX₃⟩ := s₃
  have c₁ := uc22s13xo_center_pRank hn₁ hX₁
  have c₂ := uc22s13xo_center_pRank hn₂ hX₂
  have c₃ := uc22s13xo_center_pRank hn₃ hX₃
  have hle₁ : L₁ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_left.trans le_sup_left
  have hle₂ : L₂ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right.trans le_sup_left
  have hle₃ : L₃ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right
  have hN : ∀ {A B : Subgroup G}, A ∈ calC M → B ∈ calC M → B ≤ normalizer (A : Set G) := by
    intro A B hA hB
    by_cases hAB : A = B
    · subst hAB
      exact Subgroup.le_normalizer
    · exact PartTwo.calC_le_normalizer_of_ne hA hB hAB
  have hS : ∀ L ∈ ({L₁, L₂, L₃} : Finset (Subgroup G)),
      L ∈ calC M ∧ L ≤ L₁ ⊔ L₂ ⊔ L₃ ∧ center (Bar2 L) = ⊥ ∧ CFSG.Open.pRank 3 L = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro L (rfl | rfl | rfl)
    exacts [⟨h₁, hle₁, c₁⟩, ⟨h₂, hle₂, c₂⟩, ⟨h₃, hle₃, c₃⟩]
  have h3 := P22fin3.card_le_pRank_of_finset (X := L₁ ⊔ L₂ ⊔ L₃) Nat.prime_three (by norm_num)
    (fun L hL => P22fin3.mem_calC_of_le_normalizer (hS L hL).1 (hS L hL).2.1
      (sup_le (sup_le (hN (hS L hL).1 h₁) (hN (hS L hL).1 h₂)) (hN (hS L hL).1 h₃)))
    (fun L hL => by
      rw [(hS L hL).2.2.1, Subgroup.card_bot]
      norm_num)
    (fun L hL => uc22s13xo_three_dvd_card (hS L hL).2.2.2)
  rw [Finset.card_eq_three.2 ⟨L₁, L₂, L₃, h12, h13, h23, rfl⟩] at h3
  exact ⟨PartTwo.isSubnormal_sup_sup h₁ h₂ h₃, PartTwo.commutator_sup_sup h₁ h₂ h₃, by omega,
    Or.inr ⟨L₁, L₂, L₃, h₁, h₂, h₃, c₁.2, c₂.2, c₃.2, hle₁, hle₂, hle₃,
      PartTwo.coe_sup_sup_eq_mul h₁ h₂ h₃ h12 h13 h23⟩⟩


end CFSG.LocalAnalysis.UniquenessCase.UC22
