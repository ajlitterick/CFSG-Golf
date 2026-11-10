module

public import Certificates.Data.CFSGNative.Ly.Orbit
public import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.Th.Native

structure Relabel where
  pts : Table
  pos : Table
  alpha : Table
  beta : Table
  par : Table
  lab : Table
deriving Inhabited

@[expose] def relabel (n : Nat) (alpha beta : Table) (r : Nat) : Relabel := Id.run do
  let mut pos : Table := (Array.replicate n none32).set! r 0
  let mut pts : Table := (Array.emptyWithCapacity n).push (UInt32.ofNat r)
  let mut par : Table := (Array.emptyWithCapacity n).push 0
  let mut lab : Table := (Array.emptyWithCapacity n).push 0
  for h in [0:n] do
    if h < pts.size then
      let x := ap pts h
      let ya := ap alpha x
      if ya < n && pos[ya]! == none32 then
        pos := pos.set! ya (UInt32.ofNat pts.size)
        pts := pts.push (UInt32.ofNat ya)
        par := par.push (UInt32.ofNat h)
        lab := lab.push 1
      let yb := ap beta x
      if yb < n && pos[yb]! == none32 then
        pos := pos.set! yb (UInt32.ofNat pts.size)
        pts := pts.push (UInt32.ofNat yb)
        par := par.push (UInt32.ofNat h)
        lab := lab.push 2
    else break
  let na : Table := Array.ofFn (n := pts.size) fun k => pos[ap alpha (ap pts k.val)]!
  let nb : Table := Array.ofFn (n := pts.size) fun k => pos[ap beta (ap pts k.val)]!
  return ⟨pts, pos, na, nb, par, lab⟩


end CFSG.Sporadic.LySchreier.Native
