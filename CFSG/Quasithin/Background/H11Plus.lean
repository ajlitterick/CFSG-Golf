module

public import CFSG.Quasithin.Background.H11Defs
import CFSG.Quasithin.Vol2.Ch9H11Holds
import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.D2Params
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.Quasithin.H11Proof

open CFSG.Quasithin

section PlusBridge

open scoped Matrix

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  (DeterminantIsometries determinantForm determinantForm_apply specialRho specialRho_apply)
open CFSG.Quasithin.H13


end PlusBridge

end CFSG.Quasithin.H11Proof
