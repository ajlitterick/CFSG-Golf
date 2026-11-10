module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf9Cent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

@[expose] def Wsub (K K' : Subgroup G) (y : G) : Subgroup G :=
  Subgroup.closure ((K : Set G) ∪ (K' : Set G) ∪ {y})


namespace Setting


end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
