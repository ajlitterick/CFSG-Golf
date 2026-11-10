module

public import CFSG.RankThree.PartOne.N143.SectionGroup
public import CFSG.RankThree.PartOne.N143.Statements
import CFSG.RankThree.PartOne.N143.CaseB1Theta
import CFSG.RankThree.PartOne.S10.EmbeddingTransport

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement


theorem not_dvd_card_ker_theta {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.card (QuotientGroup.mk' (aschbacherSolvableCore p X)).ker := by
  rw [QuotientGroup.ker_mk']
  exact (solvable_prime_complement_core_characterization (H := X) hp).2.2.1

theorem simple_of_quasisimple_center_bot {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (hZ : Subgroup.center Q = ⊥) :
    Nonempty (Q ⧸ Subgroup.center Q ≃* Q) ∧ IsSimpleGroup Q ∧ ∃ a b : Q, a * b ≠ b * a := by
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hq.2.1
  refine ⟨⟨e⟩, e.symm.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hq.2.2
  exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩


end CFSG.RankThree.PartOne.N143
