module

public import CFSG.ClassicalInvolution.Q3.Q3YLie
public import CFSG.ClassicalInvolution.Q3.Q3ANbhd
public import CFSG.ClassicalInvolution.Q3.Q3TAxis

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn oddCoreIn_le)

section Images

variable {G : Type} [Group G]


theorem conjSub_le_of_mem {X M : Subgroup G} (hMX : M ≤ X) {x : G} (hx : x ∈ X) :
    conjSub x M ≤ X := by
  intro y hy
  rw [mem_conjSub_iff] at hy
  have h1 := X.mul_mem (X.mul_mem hx (hMX hy)) (X.inv_mem hx)
  simpa [mul_assoc] using h1


end Images

section Link


end Link

end CFSG.ClassicalInvolution.Q3.Q3Y
