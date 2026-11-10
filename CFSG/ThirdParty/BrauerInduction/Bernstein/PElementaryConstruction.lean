module

public import CFSG.ThirdParty.BrauerInduction.Elementary.LocalFunction

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed-coset evaluation in Bernstein's proof

This file contains the part of Bernstein's local argument that evaluates the
induced local function at an element of the form `a * s`, where `a` is
`p`-regular and `s` is `p`-singular and commutes with `a`.

The evaluation is expressed as a fixed-point count on a finite coset space.
The resulting fixed-point formula is later combined with a congruence modulo
`p` to prove that the value is represented by an integer not divisible by `p`.
-/

namespace CFSG.BrauerInduction.Bernstein

section FixedCosetEvaluation


open BrauerInduction.PElementary


end FixedCosetEvaluation


end CFSG.BrauerInduction.Bernstein
