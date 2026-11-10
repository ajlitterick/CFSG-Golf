module

public import CFSG.ClassicalInvolution.Q3.Q3TSetup
public import CFSG.ClassicalInvolution.Q3.Q3WANoA1

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups commutatorElement

namespace Q3NT

theorem mul_self_eq_one_of_orderOf_eq_two {H : Type*} [Group H] {x : H} (h : orderOf x = 2) :
    x * x = 1 := by
  rw [← sq]
  exact (orderOf_eq_prime_iff.mp h).1


end Q3NT

section Component


end Component

end CFSG.ClassicalInvolution.Q3
