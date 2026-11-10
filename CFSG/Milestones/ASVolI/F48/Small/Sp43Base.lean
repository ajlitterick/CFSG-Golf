module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Geom
public import CFSG.Milestones.ASVolI.F48.Small.U42LetterData

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42

@[expose] def burnsideF48s_sp43G (i : Fin 4) : Y :=
  ⟨wordP (burnsideF48s_sp43XY.getD i []), wordP_mem _⟩


end CFSG.ASVolI
