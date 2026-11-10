module

public import Certificates.Data.CFSGNative.Fi24.Data
public import Certificates.Data.CFSGNative.Fi24.Verify
public import Certificates.Data.CFSGNative.Fi24.Sep
public import Certificates.Data.CFSGNative.Fi23.Slp
public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.Fi24.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native

set_option compiler.extract_closed false

@[expose] def decode81 (s : String) : Array Nat := Id.run do
  let ds := digits81.toList
  let tbl : Array Nat := (Array.range 128).map fun c => ds.idxOf (Char.ofNat c)
  let mut out : Array Nat := Array.mkEmpty (4 * s.length)
  for ch in s.toList do
    let x := tbl[ch.toNat]?.getD 0
    out := ((((out.push (x % 3)).push (x / 3 % 3)).push (x / 9 % 3)).push (x / 27 % 3))
  return out

@[expose] def nPts (_ : Unit := ()) : Nat := 306936

@[expose] def matA (_ : Unit := ()) : Array W := rowsOfSeed 781 seedA

@[expose] def matB (_ : Unit := ()) : Array W := rowsOfSeed 781 seedB

@[expose] def matAT (_ : Unit := ()) : Array W := transposeW 781 781 matA

@[expose] def matBT (_ : Unit := ()) : Array W := transposeW 781 781 matB

@[expose] def matF (_ : Unit := ()) : Array W :=
  let e := decode81 formData
  Array.ofFn (n := 781) fun i => ofTrits 781 fun j => e[781 * i.val + j]?.getD 0

@[expose] def initRows (_ : Unit := ()) : Array W :=
  let e := decode81 initData
  Array.ofFn (n := 253) fun i => ofTrits 781 fun j =>
    if j < 253 then (if j = i.val then 1 else 0) else e[528 * i.val + (j - 253)]?.getD 0

@[expose] def gensT (_ : Unit) : Gens := ⟨frTable matAT, frTable matBT⟩

@[expose] def rootForm (_ : Unit := ()) : RRef := rref 781 initRows


@[expose] def orbitData (_ : Unit) : Enum := enumOrbit gensT rootForm.rows 100 4096 3

@[expose] def genTables (O : Enum) (z : Int) : Table :=
  if z = 1 ∨ z = -1 then O.alpha else if z = 2 then O.beta else invT nPts O.beta

@[expose] def chainLetters (O : Enum) : Array Table := slpLetters nPts (genTables O) chainWords


end CFSG.Sporadic.Fi24.Native
