module

public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Induced
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.CoindBasic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!

# Base change for coinduction along quotient maps

Let `K` be a normal subgroup of `G`, let `π : G → G ⧸ K` be the quotient map,
and let `Q ≤ G ⧸ K`. Writing `H = π⁻¹ Q`, this file proves that pulling back
a coinduced representation along `π` agrees with coinducing the pulled-back
representation from `H` to `G`.

The main result is

* `FDRep.CoindBaseChange.comap_coind_quotient_iso`:
  `comap π (coind Q σ) ≅ coind H (comap (H → Q) σ)`.
-/

universe u v


namespace FDRep

namespace CoindBaseChange


end CoindBaseChange
end FDRep
