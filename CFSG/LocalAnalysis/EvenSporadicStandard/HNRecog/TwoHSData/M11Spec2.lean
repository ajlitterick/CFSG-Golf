module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem m11K_eq_closure :
    m11K = closure ({elemW y0Word, elemW vWord} : Set (Equiv.Perm (Fin 1408))) := by
  unfold m11K
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨y0Word, Or.inl rfl, rfl⟩
    · exact ⟨vWord, Or.inr rfl, rfl⟩


theorem m11FiveOK_spec (hg : gensOK = true) {L0 : Array Table}
    (hL0 : IsEnumSet 1408 L0 (m11K : Set (Equiv.Perm (Fin 1408)))) (h : m11FiveOK L0 = true) :
    orderOf (elemW rho0Word) = 5 ∧ elemW rho0Word ∈ m11K ∧
      (∀ k : ℕ, 0 < k → k < 5 → ∃ c ∈ m11K, c * elemW rho0Word * c⁻¹ = elemW rho0Word ^ k) ∧
      elemW cBWord * elemW rho0Word * (elemW cBWord)⁻¹ = elemW fix5B.rep := by
  simp only [m11FiveOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hB, h5⟩, hin⟩, h2⟩, h3⟩, h4⟩, hcB⟩ := h
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hrr : Rep 1408 (tabW rho0Word) (elemW rho0Word) := rep_elemW_of_gensOK hg (by decide)
  have hrB : Rep 1408 (tabW fix5B.rep) (elemW fix5B.rep) := rep_elemW_of_gensOK hg hB
  have hmem : ∀ w ∈ [rho0Word, ck2Word, ck3Word, ck4Word], elemW w ∈ m11K := by
    intro w hw
    have hwo : wordOK w = true := by
      have hw' := hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl | rfl | rfl <;> decide
    exact (hL0.memT_iff (rep_elemW_of_gensOK hg hwo)).1 (List.all_eq_true.1 hin w hw)
  refine ⟨orderOf_eq_of_primeOrderOK hrr h5, hmem _ (by simp), ?_,
    conjEqOK_spec hg hrr hrB hcB⟩
  intro k hk0 hk5
  interval_cases k
  · exact ⟨1, one_mem _, by simp⟩
  · exact ⟨elemW ck2Word, hmem _ (by simp),
      conjEqOK_spec hg hrr (Rep.powT (by norm_num) hrr 2) h2⟩
  · exact ⟨elemW ck3Word, hmem _ (by simp),
      conjEqOK_spec hg hrr (Rep.powT (by norm_num) hrr 3) h3⟩
  · exact ⟨elemW ck4Word, hmem _ (by simp),
      conjEqOK_spec hg hrr (Rep.powT (by norm_num) hrr 4) h4⟩

end CFSG.EvenSporadicStandard.HNRecog
