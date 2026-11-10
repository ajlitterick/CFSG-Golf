
module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelB0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelF1051Base
public import CFSG.Sporadic.Th.Max3.Data
public import Certificates.Certificate3018

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

namespace Mo107

open Certificates.OmegaS107


theorem mem_prod2 {cl : List P45} {x : P45} : x ∈ prod2 cl ↔ ∃ c ∈ cl, ∃ d ∈ cl, c * d = x := by
  simp [prod2, List.mem_flatMap, List.mem_map]


end Mo107

end CFSG.OddStandard.SmallF3.Omega
