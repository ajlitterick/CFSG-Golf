module

public import CFSG.Sporadic.Co1Block.TwoBCheckInputs

public section

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block

@[expose] def parseNums (s : String) : Array Nat :=
  ((s.splitOn " ").filterMap fun t => t.trimAscii.toNat?).toArray

abbrev nn : Nat := 1365

@[expose] def xa : Array Nat := twoBStrong[0]!

@[expose] def ya : Array Nat := twoBStrong[1]!

@[expose] def triTab : Array Nat := CFSG.Sporadic.Co1Block.Native.triTable twoBTris

@[expose] def brayB : List CFSG.Sporadic.Co1Schreier.Native.Rows :=
  CFSG.Sporadic.Co1Block.Native.brayElts (CFSG.Sporadic.Co1Block.Native.brayRows
    CFSG.Sporadic.Co1Schreier.Native.aR twoBD1) twoBBray

@[expose] def sa : Array Nat := CFSG.Sporadic.Co1Block.Native.triPerm triTab twoBTris brayB[5]!

@[expose] def gA : Array (Array Nat) := #[xa, ya, sa]

@[expose] def gAi : Array (Array Nat) := gA.map (invCand nn)


@[expose] def conjA (c ci t : Array Nat) : Array Nat := compA nn c (compA nn t ci)


@[expose] def buildList (init : Array Nat) (par : Array Nat) (op : Nat → Array Nat → Array Nat) :
    Array (Array Nat) :=
  (List.range par.size).foldl (fun acc k => acc.push (op k acc[par[k]!]!)) #[init]

@[expose] def conjOp (pg : Array Nat) (k : Nat) (t : Array Nat) : Array Nat :=
  conjA gA[pg[k]!]! gAi[pg[k]!]! t

@[expose] def rmulOp (gs : Array (Array Nat)) (pg : Array Nat) (k : Nat) (e : Array Nat) :
    Array Nat :=
  compA nn e gs[pg[k]!]!


@[expose] def twoBLevels : Array CFSG.Monster.B.Co2.Native.Level :=
  CFSG.Certificates.Native.rawLevels 1365 twoBStrong twoBChainBase.toArray

@[expose] def inD (g : Array Nat) : Bool := siftA nn twoBLevels twoBChainBase.toArray 0 g


@[expose] def ordAux (t : Array Nat) : Nat → Array Nat → Bool
  | 0, p => eqA nn p (idA nn)
  | d + 1, p => !eqA nn p (idA nn) && ordAux t d (compA nn t p)

@[expose] def ordIs (t : Array Nat) (v : Nat) : Bool := decide (0 < v) && ordAux t (v - 1) t

@[expose] def prodA (ls : Array (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldr (fun l acc => compA nn ls[l]! acc) (idA nn)


@[expose] def laNums : Array Nat := parseNums (include_str "G24LATbl.txt")

@[expose] def tAa : Array Nat := laNums.extract 0 1365

@[expose] def laPar : Array Nat := laNums.extract 1365 (1365 + 4094)

@[expose] def laPg : Array Nat := laNums.extract (1365 + 4094) (1365 + 2 * 4094)


@[expose] def oa : Array Nat :=
  laNums.extract (1365 + 2 * 4094 + 2 * 4095) (1365 + 2 * 4094 + 2 * 4095 + 1365)

@[expose] def laList : Array (Array Nat) := buildList tAa laPar (conjOp laPg)


end CFSG.EvenSporadicStandard.G24Aut
