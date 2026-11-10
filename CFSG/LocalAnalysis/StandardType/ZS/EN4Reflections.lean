module

public import CFSG.LocalAnalysis.StandardType.GGZSNFourFamily
public import CFSG.LocalAnalysis.StandardType.GGZSNFourSound
import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType.ZS.EN4Reflections

open Certificates.ExcModel

local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

end CFSG.StandardType.ZS.EN4Reflections
