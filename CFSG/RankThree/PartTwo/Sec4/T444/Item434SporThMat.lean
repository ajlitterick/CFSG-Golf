module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporLyMat
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.RankThree.PartTwo.Sec4.Item434SporLy (wordG wordG_mem)

abbrev Mat := Array V4

@[expose] def powRows (M : Mat) : ℕ → Mat
  | 0 => idRows
  | e + 1 => mulRows (powRows M e) M


@[expose] def powL (M : Mat) (e : ℕ) : Mat := if e = 1 then M else powRows M e


@[expose] def evalWord (gs : Array Mat) (w : List (ℕ × ℕ)) : Mat :=
  w.foldl (fun acc x => mulRows acc (powL gs[x.1]! x.2)) idRows


@[expose, reducible] def Rp (M : Mat) (g : GL (Fin 248) (ZMod 2)) : Prop :=
  rowsMatrix M = (g : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem Rp.mul {X Y : Mat} {g h : GL (Fin 248) (ZMod 2)} (hX : Rp X g) (hY : Rp Y h) :
    Rp (mulRows X Y) (g * h) := by
  unfold Rp at *
  rw [rowsMatrix_mulRows, hX, hY, Units.val_mul]

theorem Rp.eq_of_eq {X Y : Mat} {g h : GL (Fin 248) (ZMod 2)} (hX : Rp X g) (hY : Rp Y h)
    (e : X = Y) : g = h := by
  subst e
  exact Units.ext (hX.symm.trans hY)


end CFSG.RankThree.PartTwo.Sec4.Item434SporTh
