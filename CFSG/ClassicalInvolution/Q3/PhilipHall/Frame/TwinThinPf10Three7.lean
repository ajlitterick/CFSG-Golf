module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Perm

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}


@[expose] def pairVec (p q : Fin n) : Fin n → ZMod 2 :=
  fun x => (if x = p then 1 else 0) + (if x = q then 1 else 0)

theorem ofVec_pairVec_mem (p q : Fin n) : ofVec (pairVec p q) ∈ aeSub n := by
  classical
  refine ⟨?_, by simp [ofVec]⟩
  unfold wsum ofVec pairVec
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  exact zmod_two_add_self _


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
