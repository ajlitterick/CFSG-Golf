module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

public section

namespace CFSG.Quasithin.SimsG4

namespace G46Imprim

structure IsFpfInv (ε : Fin 4 → Fin 4) : Prop where
  invol : ∀ t, ε (ε t) = t
  ne : ∀ t, ε t ≠ t


theorem IsFpfInv.conj {ε π ρ : Fin 4 → Fin 4} (hε : IsFpfInv ε) (hπρ : ∀ t, π (ρ t) = t)
    (hρπ : ∀ t, ρ (π t) = t) : IsFpfInv fun t => π (ε (ρ t)) := by
  refine ⟨fun t => ?_, fun t ht => ?_⟩
  · simp only [hρπ, hε.invol, hπρ]
  · apply hε.ne (ρ t)
    have h := congrArg ρ ht
    rwa [hρπ] at h


end G46Imprim

end CFSG.Quasithin.SimsG4
