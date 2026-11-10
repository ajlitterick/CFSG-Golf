module

public import Certificates.Data.Holder1711.Om1Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylTData
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data

@[expose] def reflTab (_ : Unit := ()) : Array (Array ℕ) := (Array.range 240).map reflArr

@[expose] def wA (RT : Array (Array ℕ)) : List ℕ → Array ℕ
  | [] => idA 240
  | r :: l => compA 240 RT[r]! (wA RT l)

@[expose] def wordOK (w : List ℕ) : Bool := w.all (· < 240) && w.length % 2 == 0

@[expose] def wsA (RT : Array (Array ℕ)) (ws : List (List ℕ)) : Array (Array ℕ) :=
  (ws.map (wA RT)).toArray

@[expose] def repMasks : List ℕ := [15, 3, 252, 23]

@[expose] def eA (m : ℕ) : Array ℕ := frameArr (frameDecode m)

@[expose] def zA : Array ℕ := negArr

@[expose] def wT : List (List ℕ) := wS0 ++ wP3

@[expose] def wCa : List (List ℕ) := wSa ++ wPa3 ++ wPa5

@[expose] def wCc : List (List ℕ) := wSc ++ wPc


@[expose] def allWords : List (List ℕ) :=
  [wT0, wI0, wJ0, wS1, wG1] ++ wS0 ++ wP3 ++ wSa ++ wPa3 ++ wPa5 ++ wSc ++ wPc ++ wX ++
    wSub ++ wDT ++ maskData.map (·.2.2)


@[expose] def fCode (t : Array ℕ) : Array ℕ :=
  ((List.range 240).filter fun i => t[i]! == zA[i]!).toArray

@[expose] def actF (g : Array ℕ) (F : Array ℕ) : Array ℕ :=
  ((F.toList.map fun i => g[i]!).mergeSort fun a b => decide (a ≤ b)).toArray


@[expose] def keyF (F : Array ℕ) : ℕ := F.foldl (fun acc i => acc * 240 + i) 0

@[expose] def orbF (gs : Array (Array ℕ)) (F : Array ℕ) (fuel : ℕ) : ArrCert :=
  arrBfs (fun k X => actF gs[k]! X) gs.size keyF F fuel


@[expose] def subCerts (RT : Array (Array ℕ)) : List ArrCert :=
  wSub.map fun w => orbF (wsA RT wT) (actF (wA RT w) (fCode (eA 15))) 3151


@[expose] def evenMasks : List ℕ :=
  (List.range 256).filter fun m => framePop m % 2 == 0 && m != 0 && m != 255


@[expose] def letterA (K0 Lh : Array (Array ℕ)) (x : Array ℕ) (l : ℕ × ℕ) : Array ℕ :=
  if l.1 = 0 then K0[l.2]!
  else if l.1 = 1 then conjA 240 Lh[l.2]! x
  else conjA 240 Lh[l.2]! (invCand 240 x)

@[expose] def evalW (K0 Lh : Array (Array ℕ)) (x : Array ℕ) : List (ℕ × ℕ) → Array ℕ
  | [] => idA 240
  | l :: w => compA 240 (letterA K0 Lh x l) (evalW K0 Lh x w)

@[expose] def lettersOK (K0 Lh : Array (Array ℕ)) (w : List (ℕ × ℕ)) : Bool :=
  w.all fun l => decide (l.1 < 3) && decide (l.2 < (if l.1 = 0 then K0.size else Lh.size))


@[expose] def inDT (DT : Array (Array ℕ)) (m : Std.HashMap ℕ ℕ) (d : Array ℕ) : Bool :=
  let i := (m.get? (keyA 240 keyPts d)).getD DT.size
  decide (i < DT.size) && eqA 240 d DT[i]!


@[expose] def witOK (K0 Lh DT : Array (Array ℕ)) (m : Std.HashMap ℕ ℕ) (x : Array ℕ)
    (w : List (ℕ × ℕ)) : Bool :=
  lettersOK K0 Lh w && inDT DT m (evalW K0 Lh x w)


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
