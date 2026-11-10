module

public import CFSG.Adapters.TauCetiExceptional.MinusculeCell
public import CFSG.Adapters.TauCetiExceptional.BigCellGeneric

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg
  CFSG.TauCetiBridge.BigCell

variable (τ : Tag)


variable {τ}

variable {D : MinData τ} (hV : D.Valid) (R : Type*) [CommRing R]


variable {R} in
@[expose] def dT
    (D : MinData τ) (t : Fin τ.rank → Rˣ) : (Module.End R (Fin D.d →₀ R))ˣ :=
  diagUnit fun a => TauCeti.torusCharacter t (D.wt a)


end CFSG.TauCetiBridge.Minuscule
