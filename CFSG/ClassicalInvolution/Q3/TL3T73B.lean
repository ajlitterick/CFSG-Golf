module

public import Mathlib.Data.Fintype.Card

public section

namespace CFSG.ClassicalInvolution.Q3.Johnson

open Finset


variable {j k : ℕ}

private structure Induces (f : Finset (Fin j) → Finset (Fin k)) (T : Finset (Fin j))
    (ι : Fin j → Fin k) : Prop where
  injOn : Set.InjOn ι T
  eq : ∀ α ⊆ T, α.card = 4 → f α = α.image ι

private theorem Induces.mono {f : Finset (Fin j) → Finset (Fin k)} {T T' : Finset (Fin j)}
    {ι : Fin j → Fin k} (h : Induces f T ι) (hT : T' ⊆ T) : Induces f T' ι where
  injOn := h.injOn.mono (coe_subset.mpr hT)
  eq α hα hα4 := h.eq α (hα.trans hT) hα4


end CFSG.ClassicalInvolution.Q3.Johnson
