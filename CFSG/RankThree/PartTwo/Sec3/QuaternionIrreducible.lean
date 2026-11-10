module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartTwo.Sec3.ThreeSpaceTransvections

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Module CFSG.RankThree.Classical

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

@[expose] def commutatorSpace (H : Subgroup (V ≃ₗ[ZMod 3] V)) : Submodule (ZMod 3) V :=
  Submodule.span (ZMod 3) {y | ∃ h ∈ H, ∃ v, h v - v = y}


theorem finrank_span_pair {v w : V} (h : LinearIndependent (ZMod 3) ![v, w]) :
    finrank (ZMod 3) (Submodule.span (ZMod 3) {v, w}) = 2 := by
  have hset : Set.range ![v, w] = ({v, w} : Set V) := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  have := finrank_span_eq_card h
  rw [hset] at this
  rw [this, Fintype.card_fin]


section Core


end Core


end CFSG.RankThree.PartTwo.Sec3
