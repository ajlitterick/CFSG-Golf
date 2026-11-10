
module

public import CFSG.Monster.B.TwoA.Base.RankThreeBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.Lifts CFSG.Monster.VisCert

open CFSG.Monster.B.Co2 (v0)


theorem Shat_eq_sup : Shat = Jhat ⊔ Ntwo := by
  refine le_antisymm ?_ (sup_le Jhat_le_Shat Ntwo_le_Shat)
  rintro _ ⟨c, rfl⟩
  obtain ⟨g, rfl⟩ := kappa_surjective c
  have hg : g ∈ Subgroup.closure (((↑) : Cgen → _) ⁻¹'
      (insert tauB (Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB)))) :=
    (Subgroup.closure_closure_coe_preimage (k := insert tauB
      (Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB)))).ge (Subgroup.mem_top g)
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · refine Subgroup.mem_sup_right ?_
      have hxt : x = tauC := Subtype.ext hx
      rw [hxt]
      exact tauhat_mem_Ntwo
    · refine Subgroup.mem_sup_left ?_
      rw [Jhat_eq_map]
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  | one => rw [map_one, map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv, map_inv]; exact Subgroup.inv_mem _ hx

end CFSG.Monster.B.TwoA
