module

public import CFSG.CharacterTheory.Semidihedral.CentralizerStructure
public import CFSG.CharacterTheory.Semidihedral.AlternatingSevenExclusion
public import CFSG.Milestones.LR_dihedral_simple_recognition

public section

namespace CFSG.Semidihedral.FieldInterface

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.CentralizerResidual
open CFSG.Semidihedral.ReducedQuotients CFSG.Semidihedral.CentralizerAlternatives

variable {G : Type} [Group G] [Finite G]

theorem psl_two_field_size_ge_five {L : Type} [Group L] {p f : ℕ}
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 2 p f) :
    5 ≤ p ^ f := by
  have hthree : p ^ f ≠ 3 := by
    have hadmissible := hmodel.1
    change p.Prime ∧ 1 ≤ f ∧ 2 ≤ 2 ∧
      (2, p ^ f) ≠ (2, 2) ∧ (2, p ^ f) ≠ (2, 3) at hadmissible
    intro heq
    exact hadmissible.2.2.2.2 (by rw [heq])
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hpodd).pow
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_pow (by omega : 0 < f))
  obtain ⟨k, hk⟩ := hodd
  omega


end CFSG.Semidihedral.FieldInterface
