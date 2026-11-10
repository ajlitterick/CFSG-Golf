module

public import CFSG.ClassicalInvolution.Q3.WeakBalance
public import CFSG.ClassicalInvolution.Balance.Quotient

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KB

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Lift

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_zpowers_of_sq {x : X} (hx : x * x = 1) : IsPGroup 2 (Subgroup.zpowers x) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  show (g : X) ^ 2 = 1
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]


end Lift

section Commutator


end Commutator

end CFSG.ClassicalInvolution.Q3.Q3KB
