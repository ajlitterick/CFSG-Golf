module

public import CFSG.ThirdParty.BrauerInduction.Background.LinearChar.InducedCharacter
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Character.Iso
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.CoindBaseChange

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Descent of induced linear characters through quotients

This file contains compatibility results for induced linear characters under
quotient maps, especially when a linear character is pulled back along a
quotient.
-/

universe u v


namespace FDRep

open BigOperators


end FDRep
