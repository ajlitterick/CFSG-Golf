module

public import CFSG.Quasithin.Background.SimsF5Par
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2That

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open scoped Matrix Pointwise
open CFSG.Fischer.Classification.Beta
open CFSG.Quasithin.H13.F431.U42Aut
open CFSG.Quasithin.H13.F431.U42 (L0S wordP Xs_eq card_Xs)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45 tauFun tauPerm x45 y45 f45)

local notation "AhMat" => Matrix (Fin 6) (Fin 6) (ZMod 3)


end

end CFSG.Quasithin.SimsF5
