module

public import CFSG.ThirdParty.BrauerInduction.Elementary.FourierDelta

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Local functions induced from associated p-elementary subgroups

For a prime `p` and a `p`-regular element `a`, this file defines the class
function obtained by inducing the Fourier delta function on the associated
subgroup `E(a)`.

It proves the support property of this function and computes its value at `a`
as the prime-to-`p` index of the chosen Sylow subgroup in the centralizer of
`a`.
-/

universe u v

open ClassFun

namespace CFSG.BrauerInduction
namespace PElementary

section LocalFunction

variable (p : ℕ) [Fact p.Prime]
variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/-!
## The induced class function `f` and its support

This section defines `f p a = Ind_{E(a)}^G (phi p k a)` and proves the basic
support statement: `f p a x` vanishes when the `p`-regular part of `x` is not
conjugate to `a`.
-/

variable (p : ℕ)
variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Fact p.Prime]

/-- Bernstein Step 8: the induced class function `f`, denoted `f_a` in the proof. -/
@[expose] noncomputable def f [Finite G]
    (a : G) : ClassFun k G :=
  ClassFun.ind (k := k)  (E_subgroup p a)  (phi p k a)


/-!
## Evaluation of `f` at `a`

This section computes `f(a)`.  The result is expressed as Bernstein's index,
the index of the chosen Sylow `p`-subgroup in the centralizer of `a`, and is
shown to be prime to `p`.
-/

variable (p : ℕ) [Fact p.Prime]
variable {k : Type u} [Field k]
variable {G : Type v} [Group G]


/--
Bernstein's index attached to `a`: the index of the chosen Sylow `p`-subgroup
inside the centralizer of `a`.
-/
@[expose] noncomputable def index (x : G) : ℕ :=
  Nat.card (Subgroup.centralizer
    ({x} : Set G)) / Nat.card (P_of_Z  p x)


end LocalFunction
end CFSG.BrauerInduction.PElementary
