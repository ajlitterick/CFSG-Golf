module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov8

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.QuasithinUnique.Ch1.M22Cover CFSG.QuasithinUnique.Ch1.TitsCover
open CFSG.Monster.B CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 (rep_compA rep_idA eqA_iff eq_of_eqA allLt_iff rep_inv_of_isInvA)

@[expose] def i22hWord : List ℕ := [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
  1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0]

@[expose] def i22aVert : ℕ := 79

@[expose] def i22cj (u g v : Array ℕ) : Array ℕ := compA 22 (compA 22 u g) v

@[expose] def i22inS (T : Array (Array ℕ)) (n : ℕ) (g : Array ℕ) : Bool :=
  !allLt n fun v => !eqA 22 T[v]! g

@[expose] def i22isCore (T : Array (Array ℕ)) (n : ℕ) (h hi g : Array ℕ) : Bool :=
  i22inS T n g && i22inS T n (i22cj hi g h) && i22inS T n (i22cj h g hi)

@[expose] def i22Check (_ : Unit := ()) : Bool :=
  let T := covData.elaTab
  let n := covData.nV
  let h := wordArrP i22hWord
  let hi := invCand 22 h
  let z := compA 22 T[79]! T[79]!
  let a := T[i22aVert]!
  let ai := invCand 22 a
  (n == 128) && isInvA 22 h hi &&
  eqA 22 (compA 22 h z) (compA 22 z h) &&
  eqA 22 (compA 22 (compA 22 h h) h) (idA 22) &&
  !eqA 22 h (idA 22) &&
  aV.all (fun v => eqA 22 (compA 22 T[v]! T[v]!) z) &&
  rootsV.all (fun v => !i22inS T n (i22cj hi T[v]! h) || aV.contains v) &&
  aV.contains i22aVert && i22isCore T n h hi a && isInvA 22 a ai &&
  aV.any (fun w => eqA 22 (i22cj (compA 22 a h) ai hi) T[w]!) &&
  allLt 3 (fun i => isInvA 22 (covData.xa (fo i)) (invCand 22 (covData.xa (fo i)))) &&
  allLt n (fun v => !i22isCore T n h hi T[v]! ||
    allLt 3 fun i => i22isCore T n h hi
      (i22cj (covData.xa (fo i)) T[v]! (invCand 22 (covData.xa (fo i)))))


@[expose] noncomputable def i22hP : Equiv.Perm (Fin 22) := wordP i22hWord


theorem rep_i22h : Co2.Rep 22 (wordArrP i22hWord) i22hP := rep_wordArrP i22hWord


theorem i22_aV_lt : ∀ v ∈ aV, v < 128 := by decide

theorem i22_rootsV_lt : ∀ v ∈ rootsV, v < 128 := by decide


end CFSG.EvenSporadicStandard.M22Std
