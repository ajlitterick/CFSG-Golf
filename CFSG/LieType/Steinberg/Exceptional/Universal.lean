module

public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import CFSG.LieType.Steinberg.Adjoint.Presentation

public noncomputable section

namespace CFSG.LieType.Steinberg.Exceptional

open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal CFSG.Blueprint.Chevalley

variable (p f : ℕ) [Fact p.Prime]

abbrev e6UniversalGroup : Type := ↥(e6Data_valid.minGroup (GaloisField p f))

abbrev e6UniversalDatum : UniversalRootDatum (e6UniversalGroup p f) := e6Datum (GaloisField p f)

abbrev e7UniversalGroup : Type := ↥(e7Data_valid.minGroup (GaloisField p f))

abbrev e7UniversalDatum : UniversalRootDatum (e7UniversalGroup p f) := e7Datum (GaloisField p f)


end CFSG.LieType.Steinberg.Exceptional
