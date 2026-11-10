
module

public import CFSG.Sporadic.Fi24.OrbitBase

public section

namespace CFSG.Sporadic.Fi24.Native

open Matrix CFSG.F3.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem rowW_addW {d : ℕ} (X Y : Array W) (i : ℕ) (hi : i < d) :
    rowW (addW d X Y) i = (rowW X i).add (rowW Y i) := by
  unfold addW; rw [rowW_ofFn, dite_eq_left hi]; rfl

theorem RowsWF.addW (d : ℕ) {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y) :
    RowsWF (Native.addW d X Y) := by
  intro x hx
  unfold Native.addW at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact W.wf_add (hX.row i.val) (hY.row i.val)

theorem addW_size (d : ℕ) (X Y : Array W) : (addW d X Y).size = d := by unfold addW; simp

theorem matW_addW {d : ℕ} {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y) :
    matW d 781 (addW d X Y) = matW d 781 X + matW d 781 Y := by
  ext i j
  rw [Matrix.add_apply, matW_apply, matW_apply, matW_apply, rowW_addW X Y i.val i.isLt,
    W.val_add (hX.row _) (hY.row _)]


theorem RowsWF.zeroW (d : ℕ) : RowsWF (zeroW d) := by
  intro x hx
  unfold Native.zeroW at hx
  rw [Array.mem_replicate] at hx
  rw [hx.2]; exact W.wf_zero


section Algebra

variable (mats : Array (Array W))


variable {mats}

@[expose] def MatsOK (mats : Array (Array W)) : Prop :=
  ∀ i < mats.size, canonRows 781 mats[i]! = true

end Algebra


end CFSG.Sporadic.Fi24.Native
