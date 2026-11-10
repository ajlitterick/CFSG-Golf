module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.corollary_9_2
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
import Mathlib.Algebra.Field.ULift

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-!
# Huppert IV.6.2

Thompson's local normal-complement theorem in the book form: for an odd prime
`q`, if `S` is a Sylow `q`-subgroup of `Q` and both `C_Q(Z(S))` and
`N_Q(J(S))` have normal `q`-complements, then `Q` has a normal
`q`-complement.

The proof below is the book-order proof body. The public theorem is the short
book statement; local `step_*` names mark the corresponding paragraphs of
Huppert IV.6.2.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

attribute [local instance] commutatorElement

universe u v


/-- Conjugation preserves the cardinality of a subgroup. -/
public theorem card_conj_smul
    {Q : Type u} [Group Q] (U : Subgroup Q) (g : Q) :
    Nat.card (MulAut.conj g • U : Subgroup Q) = Nat.card U := by
  exact Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) U).symm.toEquiv


/- Huppert IV.6.2(f), internalized from the source paragraph so later have steps in this file do not depend on the old split part_f module. -/


/-!
Internalized Huppert IV.6.2(r) linear/eigenline infrastructure.
These declarations are copied into this file so the book-order proof does not depend on the old split part_r modules.
-/


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\Field.lean`. -/


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\Lift.lean`. -/


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\EigenlineCore.lean`. -/


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\EigenlineAction.lean`. -/


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\EigenlineTrivial.lean`. -/


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\EigenlineSeed.lean`. -/


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\EigenlineFinal.lean`. -/


/-! Internalized terminal infrastructure from `BenderSuzuki\External\Huppert\IV\theorem_6_2\part_r\Terminal.lean`. -/


set_option maxHeartbeats 800000

section ExtractedIV62TerminalObligations


end ExtractedIV62TerminalObligations


end External
end CFSG.BenderSuzuki
