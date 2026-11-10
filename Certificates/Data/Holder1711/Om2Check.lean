module

public import Certificates.Data.Holder1711.Om2Data
public import Certificates.Data.Holder1711.Om1Check

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
  (reflTab wA wordOK inL commOK withPairs keyF validF letterA evalW lettersOK eA)

@[expose] def pairA (a b : Array ℕ) : Array ℕ := a ++ b.map (· + 240)

@[expose] def genY (RT : Array (Array ℕ)) : Array (Array ℕ) :=
  ((List.range 8).map fun i => pairA (wA RT (omWords.getD i [])) (wA RT (yW.getD i []))).toArray

@[expose] def lettersY (RT : Array (Array ℕ)) : Array (Array ℕ) :=
  genY RT ++ (genY RT).map (invCand 480)

@[expose] def wY (LY : Array (Array ℕ)) : List ℕ → Array ℕ
  | [] => idA 480
  | l :: w => compA 480 LY[l]! (wY LY w)

@[expose] def wordYOK (w : List ℕ) : Bool := w.all (· < 16)

@[expose] def cA (k : ℕ) : Array ℕ :=
  if k = 0 then pairA negArr (idA 240) else if k = 1 then pairA (idA 240) negArr
  else pairA negArr negArr

@[expose] def fstA (a : Array ℕ) : Array ℕ := a.extract 0 240


@[expose] def keyPtsY : List ℕ := keyPts ++ keyPts.map (· + 240)

@[expose] def commY (x y : Array ℕ) : Bool := eqA 480 (compA 480 x y) (compA 480 y x)

@[expose] def res120 (a : Array ℕ) : Array ℕ := Array.ofFn (n := 120) fun j => a[(j : ℕ)]!

@[expose] def genCheck (RT : Array (Array ℕ)) : Bool :=
  yW.length == 8 && yW.all (fun w => wordOK w && validA 240 (wA RT w)) &&
    (List.range 8).all fun i =>
      eqA 120 (res120 (conjA 360 genArrs[8]! genArrs[i]!)) (pArr (wA RT (yW.getD i [])))

@[expose] def allWordsY : List (List ℕ) :=
  [wT0, wI0, wJ0, wTc, wFuseC, wLiftA, wLiftB] ++ wFuse0 ++ wS0 ++ wP3 ++ wSc ++ wPc ++ wSub ++
    wDT ++ wCR

@[expose] def wordsCheckY (RT : Array (Array ℕ)) : Bool :=
  (genY RT).all (validA 480) && wFuse0.length == 3 &&
    allWordsY.all fun w => wordYOK w && validA 480 (wY (lettersY RT) w)

@[expose] def q8ListY (x y : Array ℕ) : List (Array ℕ) :=
  let x2 := compA 480 x x
  let x3 := compA 480 x2 x
  [idA 480, x, x2, x3, y, compA 480 y x, compA 480 y x2, compA 480 y x3]

@[expose] def inLY (L : List (Array ℕ)) (a : Array ℕ) : Bool := L.any (eqA 480 a)

@[expose] def q8RelY (t x y : Array ℕ) : Bool :=
  eqA 480 (compA 480 x x) t && eqA 480 (compA 480 y y) t &&
    eqA 480 (conjA 480 y x) (invCand 480 x)

@[expose] def wT : List (List ℕ) := wS0 ++ wP3

@[expose] def wCc : List (List ℕ) := wSc ++ wPc

@[expose] def relCheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  let t0 := wY LY wT0
  let i0 := wY LY wI0
  let j0 := wY LY wJ0
  let tc := wY LY wTc
  let R0 := q8ListY i0 j0
  eqA 240 (fstA t0) (eA 15) && eqA 480 (compA 480 t0 t0) (idA 480) &&
    q8RelY t0 i0 j0 &&
    (List.range 3).all (fun k => eqA 480 (conjA 480 (wY LY (wFuse0.getD k [])) t0)
      (compA 480 t0 (cA k))) &&
    wT.all (fun w => commY (wY LY w) t0 && inLY R0 (conjA 480 (wY LY w) i0) &&
      inLY R0 (conjA 480 (wY LY w) j0)) &&
    eqA 240 (fstA tc) (eA 23) && eqA 480 (compA 480 tc tc) (idA 480) &&
    eqA 480 (conjA 480 (wY LY wFuseC) tc) (compA 480 tc (cA 1)) &&
    wCc.all (fun w => commY (wY LY w) tc) &&
    eqA 240 (fstA (wY LY wLiftA)) (eA 3) && eqA 240 (fstA (wY LY wLiftB)) (eA 252) &&
    [wLiftA, wLiftB].all (fun w =>
      !(eqA 480 (compA 480 (wY LY w) (wY LY w)) (idA 480)) &&
      !(eqA 480 (compA 480 (compA 480 (wY LY w) (cA 1)) (compA 480 (wY LY w) (cA 1)))
        (idA 480))) &&
    wCR.all (fun w => commY (wY LY w) i0 && commY (wY LY w) j0)

@[expose] def enumOfY (LY : Array (Array ℕ)) (ws : List (List ℕ)) (fuel : ℕ) : ArrCert :=
  enumBfs 480 (ws.map (wY LY)).toArray keyPtsY fuel

@[expose] def enumSizeY (LY : Array (Array ℕ)) (ws : List (List ℕ)) (sz : ℕ) : Bool :=
  let c := enumOfY LY ws (sz + 1)
  enumOK 480 (ws.map (wY LY)).toArray keyPtsY c && c.pts.size == sz

@[expose] def enumCheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  enumSizeY LY wS0 4096 && enumSizeY LY wP3 27 && enumSizeY LY wSc 1024 &&
    enumSizeY LY wPc 3 && enumSizeY LY wCR 4608

@[expose] def fCodeY (t : Array ℕ) : Array ℕ :=
  ((List.range 480).filter fun i => t[i]! == (cA 2)[i]!).toArray

@[expose] def actFY (g : Array ℕ) (F : Array ℕ) : Array ℕ :=
  ((F.toList.map fun i => g[i]!).mergeSort fun a b => decide (a ≤ b)).toArray

@[expose] def validFY (F : Array ℕ) : Bool :=
  F.all (· < 480) && (List.range (F.size - 1)).all fun i => decide (F[i]! < F[i + 1]!)

@[expose] def orbFY (gs : Array (Array ℕ)) (F : Array ℕ) (fuel : ℕ) : ArrCert :=
  arrBfs (fun k X => actFY gs[k]! X) gs.size keyF F fuel

@[expose] def orbSizeY (gs : Array (Array ℕ)) (F : Array ℕ) (sz : ℕ) : Bool :=
  let c := orbFY gs F (sz + 1)
  arrCertOK (fun k X => actFY gs[k]! X) gs.size validFY keyF F c && c.pts.size == sz

@[expose] def orbitCheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  validFY (fCodeY (wY LY wT0)) && orbSizeY (genY RT) (fCodeY (wY LY wT0)) 6300

@[expose] def inCertY (c : ArrCert) (F : Array ℕ) : Bool := c.pts.toList.any (· == F)

@[expose] def subCertsY (RT : Array (Array ℕ)) : List ArrCert :=
  let LY := lettersY RT
  wSub.map fun w => orbFY (wT.map (wY LY)).toArray (actFY (wY LY w) (fCodeY (wY LY wT0))) 6301

@[expose] def subCheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  let F0 := fCodeY (wY LY wT0)
  let gT := (wT.map (wY LY)).toArray
  let subs := subCertsY RT
  (wSub.zip subs).all (fun p => arrCertOK (fun k X => actFY gT[k]! X) gT.size validFY keyF
      (actFY (wY LY p.1) F0) p.2) &&
    (orbFY (genY RT) F0 6301).pts.toList.all (fun F =>
      F == F0 || wFuse0.any (fun w => F == actFY (wY LY w) F0) || subs.any (inCertY · F)) &&
    wSub.all (fun w => orbSizeY (gT.push (wY LY w)) F0 6300)


@[expose] def r0CheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  let L := q8ListY (wY LY wI0) (wY LY wJ0)
  L.all (validA 480) && L.all (fun a => L.all fun b => inLY L (compA 480 a b)) &&
    L.all fun a => inLY L (invCand 480 a)

@[expose] def om2CheckA (_ : Unit := ()) : Bool :=
  let RT := reflTab ()
  genCheck RT && wordsCheckY RT && relCheckY RT && enumCheckY RT && orbitCheckY RT &&
    subCheckY RT && r0CheckY RT


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
