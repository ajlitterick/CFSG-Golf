module

public import CFSG.YGroups.DoubleCosetPoints
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.YGroups

variable {G : Type*} [Group G]

namespace DoubleCosetData

variable {H C : Subgroup G} {t : G} {r : ℕ} (D : DoubleCosetData H C t r)


theorem relIndex_eq [Finite G] (hCH : C ≤ H) (ht : t * t = 1)
    (htC : ∀ c ∈ C, t * c = c * t) (hgen : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤)
    (s : Fin r → ℕ) (hs : ∀ i, (D.S i).relIndex H ≤ s i) (hsum : ∑ i, s i ≤ H.index) :
    (∀ i, (D.S i).relIndex H = s i) ∧ H.index = ∑ i, s i := by
  have hle := (D.index_le_sum hCH ht htC hgen).2
  have h1 : ∑ i, (D.S i).relIndex H = ∑ i, s i :=
    le_antisymm (Finset.sum_le_sum fun i _ => hs i) (hsum.trans hle)
  refine ⟨fun i => ?_, le_antisymm (hle.trans h1.le) hsum⟩
  exact (Finset.sum_eq_sum_iff_of_le fun i _ => hs i).1 h1 i (Finset.mem_univ i)


end DoubleCosetData

namespace SymGen.Setup


end SymGen.Setup

end CFSG.YGroups
