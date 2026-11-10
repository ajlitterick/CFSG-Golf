module

public import Certificates.Data.U62Rank.Data
public import Certificates.Data.CFSGNative.Fi22.Local
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.Monster.B.Fischer.ArrCert

public section

namespace U62Rank

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Perm.Native
  CFSG.Sporadic.Fi22.Native

@[expose] def parseNats (s : String) : Array ℕ :=
  (s.splitOn " ").toArray.filterMap fun t => t.toNat?

@[expose] def sylowGens (_ : Unit := ()) : Array (Array ℕ) :=
  ((sylowText ()).splitOn "|").toArray.map parseNats


@[expose] def commutes (a b : Array ℕ) : Bool := eqA 693 (compA 693 a b) (compA 693 b a)


end U62Rank
