module

public import Certificates.Data.CFSGNative.Co2Smith.Spin8

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

@[expose] def chainRowsN (seeds : Array (Array Nat)) (k : Nat) : Array (Array Nat) :=
  Array.map (mRows seeds) chainGens[k]!

@[expose] def chainRecN (seeds : Array (Array Nat)) (k : Nat) :
    Array Nat × Array Nat × Array Nat :=
  orbitBFS (vecStep (chainRowsN seeds k)) (chainRowsN seeds k).size chainBase[k]! 100

@[expose] def tRowsN (rec_ : Array Nat × Array Nat × Array Nat) (G : Array (Array Nat))
    (i : Nat) : Array Nat :=
  if i = 0 then idRows 22
  else if _hp : rec_.2.1[i]! < i then mulRows 22 G[rec_.2.2[i]!]! (tRowsN rec_ G rec_.2.1[i]!)
  else idRows 22
termination_by i

@[expose] def tArrN (seeds : Array (Array Nat)) : Array (Array (Array Nat)) :=
  (List.range 6).toArray.map fun k =>
    (List.range chainOrb[k]!).toArray.map (tRowsN (chainRecN seeds k) (chainRowsN seeds k))

@[expose] def sRowsN (T : Array (Array (Array Nat))) (n : Nat) : Array Nat :=
  mulRows 22 T[0]![n % 63]! (mulRows 22 T[1]![n / 63 % 32]! (mulRows 22 T[2]![n / 2016 % 15]!
    (mulRows 22 T[3]![n / 30240 % 8]! (mulRows 22 T[4]![n / 241920 % 3]!
      T[5]![n / 725760 % 2]!))))

@[expose] def aSpinN (_ : Unit := ()) : Array Int := wordZ (sp6Wa.map sCode)

@[expose] def bSpinN (_ : Unit := ()) : Array Int := wordZ (sp6Wb.map sCode)

@[expose] def mixSpinN (w : List Nat) : Array Int :=
  w.foldr (fun x acc => mulZ (if x == 2 then aSpinN else bSpinN) acc) idZ

@[expose] def tSpinN (rec_ : Array Nat × Array Nat × Array Nat) (G : Array (Array Int))
    (i : Nat) : Array Int :=
  if i = 0 then idZ
  else if _hp : rec_.2.1[i]! < i then mulZ G[rec_.2.2[i]!]! (tSpinN rec_ G rec_.2.1[i]!)
  else idZ
termination_by i


@[expose] def vecMulF (Y : Array Nat) (v : Nat) (j acc : Nat) : Nat :=
  if j < 22 then vecMulF Y v (j + 1) (if v.testBit j then acc ^^^ Y[j]! else acc) else acc
termination_by 22 - j

@[expose] def mulRowsF (X Y : Array Nat) : Array Nat := X.map fun v => vecMulF Y v 0 0

@[expose] def sRowsF (T : Array (Array (Array Nat))) (n : Nat) : Array Nat :=
  mulRowsF T[0]![n % 63]! (mulRowsF T[1]![n / 63 % 32]! (mulRowsF T[2]![n / 2016 % 15]!
    (mulRowsF T[3]![n / 30240 % 8]! (mulRowsF T[4]![n / 241920 % 3]! T[5]![n / 725760 % 2]!))))


@[expose] def mulP (a b : Array Nat × Array Int) : Array Nat × Array Int :=
  (mulRowsF a.1 b.1, mulZ a.2 b.2)


@[expose] def conjP (g gi y : Array Nat × Array Int) : Array Nat × Array Int :=
  mulP (mulP g y) gi


end CFSG.Sporadic.Co2Smith.Native
