module

public import Certificates.Data.CFSGNative.Fi22.Certificate
public import Certificates.Data.CFSGNative.Fi22.LocalData
public import Certificates.Data.CFSGNative.F4.Unitary

public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.F4.Native

set_option compiler.extract_closed false

@[expose] def t46Gen (z : Int) : Table := tvTable tvGens[z.natAbs - 1]!

@[expose] def t46Letters (_ : Unit := ()) : Array Table := buildLetters 693 t46Gen t46Words

@[expose] def t46Q (_ : Unit := ()) : Array Nat := Array.range 693

@[expose] def t46Trees (_ : Unit := ()) : Array Tree := chainTrees 693 t46Letters t46Base

@[expose] def eaPts (O : COrbit) : Array Nat :=
  ((List.range 3510).filter fun k => k != 0 && ap O.alpha k == k).toArray

@[expose] def eaPos (O : COrbit) : Array Nat := Id.run do
  let e := eaPts O
  let mut r : Array Nat := Array.replicate 3510 693
  for i in [0:e.size] do
    r := r.set! e[i]! i
  return r

@[expose] def phiInv (_ : Unit := ()) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate 693 693
  for i in [0:phiData.size] do
    r := r.set! phiData[i]! i
  return r


end CFSG.Sporadic.Fi22.Native
