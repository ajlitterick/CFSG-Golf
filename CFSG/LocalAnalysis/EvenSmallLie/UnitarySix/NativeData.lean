
module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataBase

public import CFSG.Fischer.T46Simple
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.SetOrbitTools
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificate
public meta import Certificates.Data.CFSGNative.F4.T46Simple
public meta import Certificates.Data.CFSGNative.Fi22.Local
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs
public import Certificates.Certificate3180
public import Certificates.Certificate3180Base

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Fi22.Native
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native

theorem letterT_ok : ∀ k < 46, involOK (letterT k) = true :=
  Certificates.certificate3180

@[expose] def letter (k : ℕ) (hk : k < 46) : Equiv.Perm (Fin 693) :=
  tab (involPerm (letterT k) (letterT_ok k hk))

@[expose] def u62Letters : List (Equiv.Perm (Fin 693)) :=
  (List.finRange 46).map fun k : Fin 46 => letter k k.2

@[expose] def u62W (w : List ℤ) :
    Equiv.Perm (Fin 693) := tab (evalCodes u62Letters w)

@[expose] def aGens : List (Equiv.Perm (Fin 693)) := aWords.map u62W

@[expose] def kGens : List (Equiv.Perm (Fin 693)) := kWords.map u62W

@[expose] def tGens : List (Equiv.Perm (Fin 693)) := tWords.map u62W

@[expose] def pGens : List (Equiv.Perm (Fin 693)) := aGens ++ kGens

@[expose] def sGens : List (Equiv.Perm (Fin 693)) := aGens ++ tGens

@[expose] def aQ : RawSchreierDatum 693 :=
  certificate (by decide) aGens [[2], [5], [-8, 6, 4, 1]] #v[1, 3, 45] (by decide)

@[expose] def kQ : RawSchreierDatum 693 :=
  certificate (by decide) kGens
    [[2], [1, 2, -1], [-2, -1, -2, 5, 2, 1], [-2, -1, -2, -3, 5, 3, 2, 1]] #v[0, 1, 3]
    (by decide)

@[expose] def pQ : RawSchreierDatum 693 :=
  certificate (by decide) pGens
    [[1], [2], [5], [-1, -3, -8, -11, 6, 4, 11, 1], [10, 11, -10],
      [-2, -16, -11, -10, -11, 17, 11, 10], [-7, -16, -11, -10, -11, -12, 17, 12, 11, 10]]
    #v[0, 1, 3, 45] (by decide)

@[expose] def sQ : RawSchreierDatum 693 :=
  certificate (by decide) sGens [[2], [5]] #v[1, 3, 45] (by decide)

@[expose] def tQ :
    RawSchreierDatum 693 := certificate (by decide) tGens [[3]] #v[1, 3] (by decide)

@[expose] def j1 : Equiv.Perm (Fin 693) := evalCodes aGens [1]

@[expose] def j2 : Equiv.Perm (Fin 693) := evalCodes aGens [2, 5]

@[expose] def j3 : Equiv.Perm (Fin 693) := evalCodes aGens [1, 2, 5]

@[expose] def sReps :
    List (Equiv.Perm (Fin 693)) := sRepWords.map (evalCodes sGens)

@[expose] def sConjs :
    List (Equiv.Perm (Fin 693)) := sConjWords.map u62W

@[expose] def o1 : Equiv.Perm (Fin 693) :=
  u62W [12, 17, 46, 8, -46, -17, 16, 46, 2, -46, -16, 7, 46, 2, -46, -7, 16, 46, -2, -46, -16, -12]

@[expose] def o2 :
    Equiv.Perm (Fin 693) := u62W [12, 16, 46, 2, -46, -16]

@[expose] def y2 : Equiv.Perm (Fin 693) :=
  evalCodes pGens [1, 3, 4, 9, 10, 11, 10, 11, 10, 10, 11, 10, 10]

@[expose] def chainsCheck : Bool :=
  aQ.check && aQ.orderCertificate == 512 && kQ.check && kQ.orderCertificate == 20160 &&
    pQ.check && pQ.orderCertificate == 10321920 && sQ.check && sQ.orderCertificate == 32768 &&
    tQ.check && tQ.orderCertificate == 64


@[expose] def fixCheck : Bool :=
  fixedList 693 (arrOf j3) == fixA &&
    fixA.all (fun p => (aGens.map toTable).all fun T => ap T p == p) &&
    translatesOK letterArrs fixA orbitRecord.1 orbitRecord.2.1 orbitRecord.2.2 &&
    keysSortedOK orbitRecord.1 && orbitRecord.1.size == 891


@[expose] def betaCheck : Bool :=
  beta.size == 42 && allIn 0 42 (fun i => decide (beta[i]! < 693)) &&
    decide beta.toList.Nodup &&
    (List.zip (kGens.map toTable) [g₁T, g₂T, g₃T]).all fun p =>
      allIn 0 42 fun i => ap p.1 beta[i]! == beta[p.2[i]!]!

end CFSG.EvenSmallLie.UnitarySix
