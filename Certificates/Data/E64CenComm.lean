module

public import Certificates.Data.GH74.AE117
public import CFSG.ClassicalInvolution.Q3.AE.Models
public import Std.Data.HashMap
public import CFSG.ClassicalInvolution.Q3.AE.Twins

public section

namespace Certificates.E64CenComm

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117


@[expose] def memList (_ : Unit := ()) : List (Finset (Fin 7) × Bool) :=
  fanoLines.flatMap fun ℓ => [(ℓ, true), (ℓ, false)]

@[expose] def memElts (ms : List (Finset (Fin 7) × Bool)) (k : ℕ) : List (Wr 7) :=
  memAtL (ms.getD k (∅, true)).1ᶜ (ms.getD k (∅, true)).2


end Certificates.E64CenComm
