module

public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

public section

namespace CFSG.Certificates.SetOrbit

open CFSG.Monster.B.Co2
open scoped Pointwise


@[expose] def ptSet (n : ℕ) (s : Array ℕ) : Set (Fin n) := {x | (x : ℕ) ∈ s.toList}


end CFSG.Certificates.SetOrbit
