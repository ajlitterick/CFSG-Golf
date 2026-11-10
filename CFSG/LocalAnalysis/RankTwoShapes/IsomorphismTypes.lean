module

public import CFSG.LocalAnalysis.RankTwoShapes.SylowShapes
public import CFSG.Milestones.LR_dihedral_simple_recognition
public import CFSG.CharacterTheory.Wreathed.NonabelianCentralizer
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.HallTransport
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

namespace CFSG.RankTwoShapes

open CFSG.Assembly.LowTwoRank in
theorem rank_two_isomorphism_types_of_recognitions
    (hsd : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      (∃ (S : Sylow 2 G) (n : ℕ), 4 ≤ n ∧
        Nonempty ((S : Subgroup G) ≃* CFSG.Open.SemidihedralGroup n)) →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
          CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
          CFSG.Open.StatedClassicalModel G .PSU 3 p f) ∨
      Nonempty (G ≃* CFSG.Open.StatedM11))
    (hwr : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      (∃ (S : Sylow 2 G) (n : ℕ), 2 ≤ n ∧
        Nonempty ((S : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
          CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
          CFSG.Open.StatedClassicalModel G .PSU 3 p f))
    (hlyons : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      (∃ (H : Type) (_ : Group H) (S : Sylow 2 G) (U : Sylow 2 H),
        CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
          Nonempty ((S : Subgroup G) ≃* (U : Subgroup H))) →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 2 2)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : CFSG.Assembly.twoRank G = 2) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSU 3 p f) ∨
    StatedClassicalModel G .PSU 3 2 2 ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (G ≃* StatedM11) := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
  rcases rank_two_sylow_shapes hnonab hrank S with
    ⟨n, hn, hS⟩ | ⟨n, hn, hS⟩ | ⟨n, hn, hS⟩ | ⟨H, hH, U, hmodel, he⟩
  · rcases CFSG.Milestones.lr_dihedral_simple_recognition G hnonab S n hn hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases hsd G hnonab ⟨S, n, hn, hS⟩ with
      ⟨p, f, hp, hp2, hf, -, hm⟩ | ⟨p, f, hp, hp2, hf, -, hm⟩ | h
    · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hm⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rcases hwr G hnonab ⟨S, n, hn, hS⟩ with
      ⟨p, f, hp, hp2, hf, -, hm⟩ | ⟨p, f, hp, hp2, hf, -, hm⟩
    · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hlyons G hnonab ⟨H, hH, S, U, hmodel, he⟩))))

end CFSG.RankTwoShapes
