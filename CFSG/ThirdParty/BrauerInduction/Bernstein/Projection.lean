module

public import CFSG.ThirdParty.BrauerInduction.Cyclotomic.Projection
public import CFSG.ThirdParty.BrauerInduction.Bernstein.GlobalIdeal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Bernstein's coefficient-projection step

This file applies the cyclotomic coefficient projection to Bernstein's induced
`Q`-functions.

The generator theorem `nuStar_projects_E` shows that the projection of a
function induced from a `p`-elementary subgroup lies in `BrauerSpanChar`. This
is extended to `JGlobalIdeal`. Applying `nuStarLinear` to `1 ∈ JGlobalIdeal`
yields `1 ∈ BrauerIdeal` and hence `BrauerIdeal = ⊤`.
-/

open ClassFun
open BrauerInduction.Cyclotomic

namespace CFSG.BrauerInduction
namespace Bernstein

section CharacterCoefficientProjection


end CharacterCoefficientProjection

end CFSG.BrauerInduction.Bernstein
