module

public import CFSG.ClassicalInvolution.RouteD.PatternA

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {n : ℕ}


@[expose] def addAt (t : ℕ → ZMod 2) (k : ℕ) (c : ZMod 2) : ℕ → ZMod 2 :=
  fun m => if m = k then t m + c else t m


end CFSG.ClassicalInvolution.RouteD
