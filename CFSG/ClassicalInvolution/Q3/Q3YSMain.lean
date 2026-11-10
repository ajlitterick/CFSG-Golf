module

public import CFSG.ClassicalInvolution.Q3.Q3YSLift
public import CFSG.ClassicalInvolution.Q3.Q3YSInputs
public import CFSG.ClassicalInvolution.Q3.Q3WAAllA1
public import CFSG.ClassicalInvolution.Q3.Q3ZTop

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement


section FourGroup


end FourGroup

section Comp


theorem zTwo_of_valid (c : CompData) (hv : c.Valid) (hc : c ≠ CompData.sl23) :
    ∀ f : c.G, (∀ m : c.G, ⁅f, m⁆ ∈ Subgroup.center c.G) → f ∈ Subgroup.center c.G := by
  rcases hv with ⟨t, n, hfund, hadm, rfl⟩ | rfl | rfl
  · have hq := ModelFacts.isQuasisimple_modelUniv t n 3 1 Nat.prime_three hfund hadm
    have : Group.IsPerfect (CompData.model t n).G := ⟨hq.1⟩
    exact fun f hf => mem_center_of_commutators_central hf
  · exact absurd rfl hc
  · intro f hf
    have hcen : Subgroup.center CompData.m11.G = ⊥ := Q3W.center_m11_eq_bot
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := hf g
    rw [hcen, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at h1
    exact h1.symm


end Comp

end CFSG.ClassicalInvolution.Q3.Q3YS
