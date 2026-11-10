
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpInputs

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

theorem rowsMatrix_ne_of_rowsDiffer {X Y : Array V4} (h : rowsDiffer X Y = true) :
    rowsMatrix X ≠ rowsMatrix Y := by
  unfold rowsDiffer at h
  simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨k, hk, c, hc, hne⟩ := h
  intro heq
  have h1 := congrFun (congrFun heq ⟨k, hk⟩) ⟨c, hc⟩
  rw [rowsMatrix_apply, rowsMatrix_apply, V4.toVec_apply, V4.toVec_apply] at h1
  apply hne
  unfold rowAt
  revert h1
  cases (X[k]?.getD V4.zero).testBit c <;> cases (Y[k]?.getD V4.zero).testBit c <;> decide


theorem getElem!_setIfInBounds_of_lt {α : Type*} [Inhabited α] {R : Array α} {k r : ℕ}
    (hr : r < R.size) (x : α) :
    (R.setIfInBounds k x)[r]! = if k = r then x else R[r]! := by
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_setIfInBounds,
    getElem!_pos R r hr]

theorem opRows_size (R : Array (Array V4)) (op : Op) : (opRows R op).size = R.size := by
  cases op <;> simp [opRows]


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
