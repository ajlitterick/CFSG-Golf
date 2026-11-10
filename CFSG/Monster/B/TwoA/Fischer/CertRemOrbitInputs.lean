module

public import CFSG.Monster.B.TwoA.Fischer.CertSeed
public import CFSG.Monster.B.TwoA.Fischer.CertRemText
public meta import CFSG.Monster.B.TwoA.Fischer.CertSeed
public meta import CFSG.Monster.B.TwoA.Fischer.CertRemText
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open Lean (Json)
open CFSG.Monster.B.Fischer CFSG.Monster.B.Binary.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] def remSeed : ℕ := 16058837527637121392057


@[expose] def treeOK (vecs pars gens : Array ℕ) : Bool :=
  vecs.size == 694980 && vecs[0]! == remSeed &&
    ((List.range 694980).all fun i =>
      decide (vecs[i]! < 2 ^ 78) &&
        (i == 0 || (decide (pars[i]! < i) && decide (gens[i]! < 4) &&
          vecs[i]! == vecMulN 78 (fourColArr[gens[i]!]!) vecs[pars[i]!]!))) &&
    strictSorted (vecs.toList.mergeSort)


end CFSG.Monster.B.TwoA.Fischer.Cert
