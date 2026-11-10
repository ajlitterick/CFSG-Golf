module

public import CFSG.ThirdParty.BrauerInduction.Elementary.PElementary

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Brauer elementary groups

This file contains an API for Brauer elementary groups.

A group is **Brauer elementary** if it is `p`-elementary for some prime `p`.

 -/

universe u v

namespace CFSG.BrauerInduction

/--
A group is **Brauer elementary** if it is `p`-elementary for some prime `p`.
-/
@[expose] def IsBrauerElementary (G : Type u) [Group G] : Prop :=
  ∃ p : ℕ, p.Prime ∧ IsPElementary p G

namespace IsBrauerElementary


end IsBrauerElementary

end CFSG.BrauerInduction
