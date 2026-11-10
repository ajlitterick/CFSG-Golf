module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutEModel
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.M12.Statements

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.EvenSporadicStandard.Fin76b CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.M12 AutETable

@[expose] def pB : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

@[expose] def sP : Equiv.Perm (Fin 12) := pB * bfF * bfF * pB

@[expose] def u1P : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [1, 2] * List.formPerm [5, 10] * List.formPerm [6, 9]

@[expose] def tbl14 (σ : Equiv.Perm (Fin 12)) : Table :=
  (Array.range 14).map fun i =>
    if h : i < 12 then ((σ ⟨i, h⟩ : Fin 12).val.toUInt32) else i.toUInt32

@[expose] def tauT : Table :=
  (Array.range 14).map fun i =>
    if i = 12 then (13 : UInt32) else if i = 13 then 12 else i.toUInt32

@[expose] def yGens : Array Table := #[tauT, tbl14 bfE, tbl14 bfN, tbl14 bfF, tbl14 sP]

@[expose] def tGens : Array Table := #[tauT, tbl14 bfE, tbl14 bfN, tbl14 bfF]

@[expose] def cT : Table := tbl14 bfJ

@[expose] def sT : Table := tbl14 sP

@[expose] def u1T : Table := tbl14 u1P

@[expose] def yE : Array Table × Array ℕ × Array ℕ := mulClosureS 14 14 yGens 2000

@[expose] def yEl : Array Table := yE.1

@[expose] def tE : Array Table × Array ℕ × Array ℕ := mulClosureS 14 14 tGens 1000

@[expose] def tEl : Array Table := tE.1

@[expose] def yMul (a b : ℕ) : ℕ := tblMulIdx 14 yEl a b

@[expose] def yM : Array (Array ℕ) := tab2 384 yMul


@[expose] def ixOf (T : Table) : ℕ :=
  ((List.range yEl.size).find? fun k => tblEq 14 yEl[k]! T).getD 0


@[expose] def tIdx : List ℕ := tEl.toList.map ixOf


@[expose] def fT : Bool :=
  tIdx.length == 128 && tEl.toList.all (fun T => tblEq 14 yEl[ixOf T]! T) &&
    (tIdx.filter fun k => mt yM k k == 0).length == 56 &&
    tblEq 14 yEl[ixOf u1T]! u1T && tIdx.contains (ixOf u1T)


@[expose] def fT8 : Bool := tIdx.any fun t => mt yM (mt yM t t) (mt yM t t) != 0


end CFSG.EvenSporadicStandard.M12Std.Yosh
