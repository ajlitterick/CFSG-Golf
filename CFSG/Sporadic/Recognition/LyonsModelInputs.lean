module

public import CFSG.Sporadic.Recognition.McLMultiplierInputs
public import CFSG.Sporadic.Recognition.LyonsModelData

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Recognition.McLMultiplier CFSG.LieType.Multipliers

abbrev deg : ℕ := 66825

@[expose] def decodeWord (s : String) : List ℤ :=
  s.toList.map fun ch =>
    if ch = 'c' ∨ ch = 'a' then 1 else if ch = 'C' ∨ ch = 'A' then -1 else
    if ch = 'd' ∨ ch = 'b' then 2 else -2


@[expose] def wordA : List ℤ :=
  decodeWord
    "cdcddcdcdcddcdcdcdcddcdcdcddcdcdcdcddcdcdcddcdcdcdcddcdcdcddcdcdcdcddcdcdcddcdcdcdcddcdc\
     dcddcdcdcdcddcdcdcddcdcdcdcddcdcdcddcdcdcdcddcdcdcddcdcdcdcddcdcdcddcdcdcdcddcdcdcddcdcd\
     cdcddcdcdcddcdcd"

@[expose] def wordB : List ℤ :=
  decodeWord
    "DDCDDCDcddcdcddcdcddcddcddcdd"

@[expose] def wordD : List ℤ :=
  decodeWord
    "bABABBABABBBBABABBBABABBABABABABBABABBBBABABBBABABBABABBBBABABBABABBBBABABBBABABBABABBAB\
     ABBABABBBBABABBBABABBABABaBaBaBaBABBABBBABABABABABABBA"

@[expose] def wordCAC : List ℤ :=
  decodeWord
    "BBABABBABABBBBABABBBABABBABABBABABBABABBBBABABBBABABBABABABABBABABBBBABABBBABABBABABABAB\
     BABABBBBABABBBABABBABABABABBABABBBBABABBBABABBABABBABABBABABABABABBBABABBBBABBBABBABABBB\
     ABABAABBAbABABBBBABBBABBABBBAAABBABAAAAABBBBABABBBAAAbbABABBABABBBBABABBBABABBABABABABBA\
     BABBBBABABBBABABBABABABABBABABBBBABABBBABABBABABBABABBABABABABABBBABABBBBABBBABBABABBBAB\
     ABAABABBABABBBBABABBBABABBABABABABBABABABABABBBABABBBBABBBABBABABBBABABAABABBABABABABABB\
     BABABBBBABBBABBABABBBABABAABBABABABABBABABB"

@[expose] def wordCBC : List ℤ :=
  decodeWord
    "bbbabbabababbabAbbABababbbababbabbbabbbbababbbabababababbabababababbbababbabbbabbbbababb\
     babababababbababababbababbbababbbbababbababbbababbababbbababbbbababbabaBabababbbababbabb\
     babbbbababbbabababababbababbababbababbbababbbbababbabaabababbbababbabbbabbbbababbbababab\
     ababbababababbababbbababbbbababbababbbbababbababbbababbbbababbababababbababbbababbbbabab\
     bababababbababbbababbbbababbabab"

@[expose] def wordY : List ℤ :=
  decodeWord
    "CDcdcDcdcDcdcDcdcDCdCDCdCdcDcdcDcDcdcDcDcddCDCdCDCDCDCCDCCCDCCdCDCdCDCDCDCCDCCCDCdCDCdCD\
     CDCDCCDCCCDCCdCDCdCDCDCDCCDCCCDCdCDCdCDCDCDCCDCCCDCdCDCdCDCDCDCCDCCCDCDCDDCdCDCdCDCDCDCC\
     DCCCDCdCDCDCDCDCDCDCDCDCDDCDCDCDCDCDCDCDCDCDCdCdCDCdCDCDCdCDCDcdcdcDcdcdcDcdcDcD"

@[expose] def wordT0 : List ℤ :=
  decodeWord
    "cddcdcddcdcddcdcdcdcddcdcddcddcddcdcddcdcddcdcdcdcddcdcddcddcddcdcddcdcddcdcdcdcddcdcddc\
     ddcddcdcddcdcddcdcdcdcddcdcddcdd"

@[expose] def wordX : List ℤ :=
  decodeWord
    "CdCdCDCdCDCDCdCDCDcdcdcDcdcdcDcdcDcD"

@[expose] def wordU1 : List ℤ :=
  decodeWord
    "c"

@[expose] def wordU2 : List ℤ :=
  decodeWord
    "DcdcDcdcDcdCDCdCDCd"

@[expose] def wordU3 : List ℤ :=
  decodeWord
    "dcdcdcDcDcDcdcDcdCDCdCdCdCDCDCD"

@[expose] def wordU4 : List ℤ :=
  decodeWord
    "dcdcdcDcdcdcdcdcDCdCdCdCdCDCDCdCd"

@[expose] def wordF : List ℤ :=
  decodeWord
    "DCdCDCdCDCdCDCdCDCdCdcdcdcDcdcdcdcdcDcdcdcdcdcDcDcdcddCdCdCDCDCDCdCDCdCDCdCdCdCDCDCDDCDC\
     dCdCDCDCDCDCdCDCDCDCDCdCDCDCDdcdcdcDcDcDcdcDcdcDcdcdcdcDcDcDDcdcDcdcDcdcDcdcDcdcDCDCdCdC\
     DCDCDCDCdCDCDCDCDCdCDCDCDcDCDCdCdCDCDCDCDCdCDCDCDCDCdCDCDCDDCdCDCdCDCdCDCdCDCd"

@[expose] def wordN : List ℤ :=
  decodeWord
    "cDcdcDcdcDcdcDcdcDcddcdcdcDcdcdcdcdcDcdcdcdcdcDcDcdcdCdCdCdCDCDCDCdCDCdCDCdCdCdCDCDCDCdC\
     dCdCDCDCDCdCDCdCDCdCdCdCDCDCDCDCDCdCdCDCDCDCDCdCDCDCDCDCdCDCDCDdCdCdCDCDCDCdCDCdCDCdCdCd\
     CDCDCDCdcdcdcDcdcdcdcdcDcdcdcdcdcDcDcdcddCdCdCDCDCDCdCDCdCDCdCdCdCDCDCDC"

@[expose] def wordGg : List ℤ :=
  decodeWord
    "dcdcdcDcdcdcdcdcDcdcdcdcdcDcDcdcdCdCdCdCDCDCDCdCDCdCDCdCdCdCDCDCDCdCdCdCDCDCDCdCDCdCDCdC\
     dCdCDCDCDCDCDCdCdCDCDCDCDCdCDCDCDCDCdCDCDCDdcdcdcDcDcDcdcDcdcDcdcdcdcDcDcDDCDCdCdCDCDCDC\
     DCdCDCDCDCDCdCDCDCDcdcdcdcDcdcdcdcdcDcdcdcdcdcDcDcdcd"

@[expose] def wordConj : List ℤ :=
  decodeWord
    "DDCDDCDCDDCDCDDCDDCDCDD"

@[expose] def hexVal (b : UInt8) : ℕ := if 97 ≤ b.toNat then b.toNat - 87 else b.toNat - 48

@[expose] def tabOfHex (s : String) : Table :=
  let b := s.toUTF8
  Array.ofFn (n := deg) fun i =>
    let j := 5 * i.val
    UInt32.ofNat ((((hexVal b[j]! * 16 + hexVal b[j + 1]!) * 16 + hexVal b[j + 2]!) * 16 +
      hexVal b[j + 3]!) * 16 + hexVal b[j + 4]!)

@[expose] def cT : Table := tabOfHex cTabHex

@[expose] def dT : Table := tabOfHex dTabHex

@[expose] def letterOf (tabs invs : Array Table) (l : ℤ) : Table :=
  if 0 < l then tabs[(l - 1).toNat]! else invs[(-l - 1).toNat]!

@[expose] def wT (tabs invs : Array Table) : List ℤ → Table
  | [] => idT deg
  | l :: w => compT deg (letterOf tabs invs l) (wT tabs invs w)

@[expose] def permOK (n : ℕ) (T R : Table) : Bool :=
  decide (T.size = n) && decide (R.size = n) &&
    allIn 0 n fun i => decide (ap T i < n) && decide (ap R i < n) && ap R (ap T i) == i &&
      ap T (ap R i) == i

@[expose] def tabs0 : Array Table := #[cT, dT]

@[expose] def invs0 : Array Table := tabs0.map (invT deg)

@[expose] def tabs1 : Array Table := #[wT tabs0 invs0 wordA, wT tabs0 invs0 wordB]

@[expose] def invs1 : Array Table := tabs1.map (invT deg)

@[expose] def tabs2 : Array Table := (Array.range 6).map fun k => wT tabs1 invs1 (mclGenWord k)

@[expose] def invs2 : Array Table := tabs2.map (invT deg)

@[expose] def tabA : Table := tabs1[0]!

@[expose] def tabB : Table := tabs1[1]!

@[expose] def tabR0 : Table := wT tabs2 invs2 (mclR0.map letterZ)

@[expose] def tabX : Table := invT deg tabR0

@[expose] def tabYw : Table := wT tabs0 invs0 wordY

@[expose] def tabF : Table := wT tabs0 invs0 wordF

@[expose] def tabN : Table := wT tabs0 invs0 wordN

@[expose] def tabG : Table := wT tabs0 invs0 wordGg

@[expose] def wordW : List ℤ := wordConj ++ invW wordY ++ invW wordConj

@[expose] def tabW : Table := wT tabs0 invs0 wordW

@[expose] def tabWinv : Table := wT tabs0 invs0 (invW wordW)

@[expose] def tabYinv : Table := wT tabs0 invs0 (invW wordY)

@[expose] def uWords : List (List ℤ) := [wordU1, wordU2, wordU3, wordU4]

@[expose] def uTabs : Array Table := (uWords.map (wT tabs0 invs0)).toArray

@[expose] def uInvTabs : Array Table := (uWords.map fun w => wT tabs0 invs0 (invW w)).toArray

@[expose] def tabCheck : Bool :=
  permOK deg cT invs0[0]! && permOK deg dT invs0[1]! &&
    (List.range 2).all (fun k => invOK deg tabs1[k]! invs1[k]!) &&
    (List.range 6).all fun k => invOK deg tabs2[k]! invs2[k]!

@[expose] def coverCheck : Bool :=
  mclCover.all fun r => wT tabs2 invs2 (r.map letterZ) == idT deg

@[expose] def structCheck : Bool :=
  invOK deg tabR0 tabX && !(tabR0 == idT deg) &&
    (compT deg tabR0 (compT deg tabR0 tabR0) == idT deg) &&
    (tabs2[5]! == tabA) &&
    (tabB == compT deg (wT tabs2 invs2 (mclSurjB.map letterZ)) (compT deg tabX tabX)) &&
    (wT tabs0 invs0 wordX == tabX) &&
    (dT == wT tabs1 invs1 wordD) &&
    (compT deg cT (compT deg tabA invs0[0]!) == wT tabs1 invs1 wordCAC) &&
    (compT deg cT (compT deg tabB invs0[0]!) == wT tabs1 invs1 wordCBC) &&
    (compT deg cT cT == idT deg) &&
    (compT deg cT (compT deg tabX invs0[0]!) == tabR0)

@[expose] def cp1Check : Bool :=
  (compT deg tabYw tabX == compT deg tabX tabYw) &&
    (compT deg tabYw (compT deg tabYw tabYw) == idT deg) &&
    !(tabYw == idT deg) && !(compT deg tabYw tabYw == tabR0) && !(tabYw == tabR0) &&
    (powT deg 5 tabF == idT deg) && !(tabF == idT deg) &&
    (compT deg tabF tabYw == compT deg tabYw tabF) &&
    (compT deg tabN (compT deg tabYw (wT tabs0 invs0 (invW wordN))) == tabYw) &&
    (compT deg tabN (compT deg tabX (wT tabs0 invs0 (invW wordN))) == tabR0)

@[expose] def invCheck : Bool :=
  (compT deg tabG (compT deg tabX (wT tabs0 invs0 (invW wordGg))) == tabR0) &&
    (compT deg tabG (compT deg tabYw (wT tabs0 invs0 (invW wordGg))) == tabYw ||
      compT deg tabG (compT deg tabYw (wT tabs0 invs0 (invW wordGg))) == tabYinv) &&
    (compT deg tabG (compT deg tabW (wT tabs0 invs0 (invW wordGg))) == tabW ||
      compT deg tabG (compT deg tabW (wT tabs0 invs0 (invW wordGg))) == tabWinv) &&
    (List.range 4).all fun j =>
      compT deg uTabs[j]! (compT deg tabYw uInvTabs[j]!) == tabYw ||
        compT deg uTabs[j]! (compT deg tabYw uInvTabs[j]!) == tabYinv

@[expose] def tabT0 : Table := wT tabs0 invs0 wordT0

@[expose] def markCheck : Bool :=
  (compT deg tabT0 tabT0 == idT deg) && !(tabT0 == idT deg) &&
    (compT deg tabT0 tabX == compT deg tabX tabT0) &&
    (compT deg tabT0 tabYw == compT deg tabYw tabT0) &&
    (compT deg tabT0 tabW == compT deg tabW tabT0)


@[expose] def evalPt (w : List ℤ) (q : ℕ) : ℕ :=
  w.foldr (fun l q => ap (letterOf tabs0 invs0 l) q) q


structure Cp3Data where
  sets : Array (Array UInt32)
  par : Array (ℕ × ℕ)
  words : Array (List ℤ)
  wit : Array ℕ
  orb : Array ℕ
  opar : Array (ℕ × ℕ)

@[expose] def conjPt (g : List ℤ) (q : ℕ) : ℕ :=
  evalPt g (ap tabYw (evalPt (invW g) q))


end CFSG.Sporadic.Recognition.LyonsSims.Ly0
