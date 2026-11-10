module

public import CFSG.Sporadic.SmallOddCore.LocalCheck
public import CFSG.Sporadic.SmallOddCore.HSCheckInputs
public import CFSG.Sporadic.Recognition.HSMultiplierInputs

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.HSMultiplier

@[expose] def evalW {ι : Type} (n : ℕ) (g gi : ι → Table) (w : List (ι × Bool)) : Table :=
  w.foldl (fun acc l => compT n acc (if l.2 then g l.1 else gi l.1)) (idT n)

@[expose] def tComm (n : ℕ) (a b : Table) : Table :=
  compT n (compT n a b) (compT n (invT n a) (invT n b))


@[expose] def harHex : String := include_str "HarModelTbl.txt"

@[expose] def harY (i : Fin 6) : Table := hexT 4 11200 (11200 * i.val) harHex

@[expose] def harYI (i : Fin 6) : Table := invT 11200 (harY i)

@[expose] def harYs : List Table := (List.finRange 6).map harY

@[expose] def harModelOK : Bool :=
  (List.finRange 6).all (fun i => permOK 11200 (harY i) && invOK 11200 (harY i) (harYI i)) &&
  hsRels.all (fun r => (List.finRange 6).all fun i =>
    commTT 11200 (harY i) (evalW 11200 harY harYI r)) &&
  (List.finRange 6).all (fun i =>
    tblEq 11200 (evalW 11200 harY harYI (hsCommWord i)) (harY i))

@[expose] def harA (i : Fin 2) : Table := hsPGTbls[i.val]!

@[expose] def harAI (i : Fin 2) : Table := hsPGInvTbls[i.val]!

@[expose] def harX (i : Fin 6) : Table := evalW 3850 harA harAI (hsGenWords.getD i.val [])

@[expose] def harXI (i : Fin 6) : Table := invT 3850 (harX i)

@[expose] def harXs : List Table := (List.finRange 6).map harX

@[expose] def harPOK : Bool :=
  (List.finRange 2).all (fun i => permOK 3850 (harA i) && invOK 3850 (harA i) (harAI i)) &&
  (List.finRange 6).all (fun i => permOK 3850 (harX i) && invOK 3850 (harX i) (harXI i)) &&
  hsRels.all (fun r => tblEq 3850 (evalW 3850 harX harXI r) (idT 3850)) &&
  (List.finRange 6).all (fun i =>
    tblEq 3850 (evalW 3850 harX harXI (hsCommWord i)) (harX i)) &&
  tblEq 3850 (evalW 3850 harX harXI hsSurjA) (harA 0) &&
  tblEq 3850 (evalW 3850 harX harXI hsSurjB) (harA 1)

@[expose] def harUW : List (List ℕ) :=
  [[5, 2, 6, 5], [1, 3, 4, 5, 3, 2, 3, 6, 3, 1, 6, 4, 3],
    [1, 3, 2, 3, 2, 4, 3, 2, 3, 5, 4, 3, 2, 3, 6, 5, 3, 4, 2, 3]]

@[expose] def harU : List Table := harUW.map (wordTbl 11200 harYs)

@[expose] def harUX : List Table := harUW.map (wordTbl 3850 harXs)

@[expose] def tU (w : List ℕ) : Table := wordTbl 11200 harU w

@[expose] def tUX (w : List ℕ) : Table := wordTbl 3850 harUX w

@[expose] def harCPairs : List (List ℕ × List ℕ) :=
  [([2, 1, 2, 2, 3, 1, 3], [1, 3, 1, 3, 2, 3]), ([2, 1, 2, 3, 1, 3, 3], [2, 1, 3, 2, 1, 2, 3, 3]),
    ([2, 3, 2, 3, 3, 1], [1, 3, 2, 1, 3, 3, 1, 3]), ([1, 3, 2, 3], [2]),
    ([1, 3, 2, 2, 3, 3], [1, 2, 3, 3, 3, 2])]

@[expose] def harCgens : List Table := harCPairs.map fun p => tComm 11200 (tU p.1) (tU p.2)

@[expose] def harWgens : List Table := harCgens ++ [tU [1], tU [2, 3, 3]]

@[expose] def harC0 : Table := tU [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]

@[expose] def harZ1 : Table := tU [3, 3, 3, 3]

@[expose] def harZ2 : Table := compT 11200 harC0 harZ1


end CFSG.EvenSporadicStandard.TwoHS
