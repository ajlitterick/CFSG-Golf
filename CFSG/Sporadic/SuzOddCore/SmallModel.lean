module

public import CFSG.Sporadic.SuzOddCore.CertChain
public import CFSG.Sporadic.SuzOddCore.LiftedValid

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2


@[expose] def suzEquivM :
    Blueprint.NativeSporadic.Suz ≃* suzM := suzEquivP.trans suzTheta


theorem suzM_not_comm :
    ∃ x y : suzM, x * y ≠ y * x := by
  by_contra h
  have h' : ∀ x y : suzM, x * y = y * x := fun x y => by
    by_contra hxy
    exact h ⟨x, y, hxy⟩
  have : IsMulCommutative suzM := ⟨⟨h'⟩⟩
  have hp := (Group.is_simple_iff_prime_card (α := suzM)).1 suzM_isSimpleGroup
  rw [suzM_card] at hp
  norm_num at hp


end CFSG.Sporadic.SuzOddCore
