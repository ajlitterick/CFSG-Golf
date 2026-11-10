module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Nilpotent-group helper lemmas

This file contains group-theoretic lemmas about nilpotent groups used in the
representation-theoretic induction arguments, especially the extraction of
nontrivial central elements from nontrivial normal subgroups.
-/

universe u

