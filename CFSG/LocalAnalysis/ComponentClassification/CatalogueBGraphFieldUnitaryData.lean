module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldScalarFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldScalarUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldNonidentity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoFieldData

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearInner CatalogueBUnitaryIsometry
open CatalogueBUnitaryTwo CFSG.LieType.Universal.Unitary

universe u


abbrev UnitaryDataProjectiveSpecial (n : ℕ) (K : Type u) [Field K] [Finite K]
    (r e : ℕ) [Fact r.Prime] (hcard : Nat.card K = (r ^ e) ^ 2) :=
  ProjectiveSpecialUnitary n K (unitaryFieldConjugation r e hcard)


end

end CFSG.ComponentClassification.CatalogueBGraphField
