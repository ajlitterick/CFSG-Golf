module

public import Certificates.Data.CFSGNative.Fi24.Enum

public section

namespace CFSG.Sporadic.Fi24.Native

open CFSG.Sporadic.Th.Native

@[expose] def formAt (gens : Unit → Gens) (E : Enum) (R0 : RRef) (k : Nat) : RRef :=
  if _h : 0 < k ∧ ap E.par k < k then
    stepForm ((gens ()).get (ap E.lab k)) (formAt gens E R0 (ap E.par k)).rows
  else R0
termination_by k

@[inline, expose] def Enum.st (E : Enum) (m : Nat) : Nat := E.starts[m]!


@[expose] def enumOK (E : Enum) (n : Nat) : Bool :=
  let L := E.starts.size
  E.alpha.size == n && E.beta.size == n && E.par.size == n && E.lab.size == n &&
    3 ≤ L && E.st 0 == 0 && E.st 1 == 1 && E.st (L - 1) == n && ap E.lab 0 == 0 &&
    allIn 0 (L - 1) (fun m => E.st m < E.st (m + 1)) &&
    allIn 0 n (fun k => ap E.alpha k < n && ap E.beta k < n) &&
    invoOK n E.alpha && order3OK n E.beta &&
    allIn 1 (L - 1) (fun m => allIn (E.st m) (E.st (m + 1)) fun k =>
      let p := ap E.par k
      let l := ap E.lab k
      E.st (m - 1) ≤ p && p < E.st m &&
        ((l == 1 && ap E.alpha p == k) || (l == 2 && ap E.beta p == k)))


end CFSG.Sporadic.Fi24.Native
