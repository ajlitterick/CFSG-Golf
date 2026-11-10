module

public import CFSG.Sporadic.ONOddCore.QuotTauIso
public import CFSG.Sporadic.ONOddCore.QuotSigma

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_record
    {d f g : ℕ} (hd : d < 3) (hf : f < 2) (hg : g < 2) :
    ∃ k < 12, (recK k).diag = d ∧ (recK k).field = f ∧ (recK k).graph = g := by
  refine ⟨4 * d + 2 * f + g, by omega, ?_⟩
  have h := recK_triple (k := 4 * d + 2 * f + g) (by omega)
  interval_cases d <;> interval_cases f <;> interval_cases g <;> simpa [tripleList] using h


end CFSG.Sporadic.ONOddCore
