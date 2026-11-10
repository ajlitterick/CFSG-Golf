module

public import CFSG.ThirdParty.BrauerInduction.Bernstein.PrimeToP
public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.PrimePowerCongruence
public import CFSG.ThirdParty.BrauerInduction.Elementary.LocalSum

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Bernstein's congruences modulo prime powers

For each prime `p` and exponent `r`, this file raises the fixed-prime local sum
to the Euler-totient power `φ(p ^ r)`.

The resulting element remains in Bernstein's fixed-prime ideal and is
pointwise congruent to `1` modulo `p ^ r`.
-/

universe u

namespace CFSG.BrauerInduction.Bernstein

variable {k G : Type u} [Field k] [Group G]
variable (p r : ℕ) [Fact p.Prime]

/--
The Euler-totient power of Bernstein's fixed-prime local sum.
-/
@[expose] noncomputable def localSumPower
    [Finite G] [CharZero k] [IsAlgClosed k] :
    ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G) :=
  PElementary.localSumElement p ^ (p ^ r).totient

@[simp]
lemma coe_localSumPower
    [Finite G] [CharZero k] [IsAlgClosed k] :
    (localSumPower (k := k) (G := G) p r : ClassFun k G) =
        PElementary.localSum (k := k) p ^ (p ^ r).totient :=
  rfl


end CFSG.BrauerInduction.Bernstein
