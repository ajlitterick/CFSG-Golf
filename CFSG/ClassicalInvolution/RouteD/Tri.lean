module

public import CFSG.ClassicalInvolution.RouteD.Basic

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {n : ℕ}


@[expose] def next (θ : Fin n → ℤ) (i : Fin n) : ℤ :=
  if h : i.val + 1 < n then θ ⟨i.val + 1, h⟩ else 0


end CFSG.ClassicalInvolution.RouteD
