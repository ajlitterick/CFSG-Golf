module

public import Certificates.Data.YamakiEnum

public section

namespace CFSG.CGT.Foote82.InvolA6

open CFSG.ClassicalInvolution.Solomon73.Yamaki

@[inline, expose] def anyLt (n : ℕ) (p : ℕ → Bool) : Bool := Nat.any n fun i _ => p i


@[expose] def invArr (t : Array ℕ) : Array ℕ :=
  (List.range 64).foldl (fun r j => r.set! t[j]! j) (Array.replicate 64 0)


end CFSG.CGT.Foote82.InvolA6
