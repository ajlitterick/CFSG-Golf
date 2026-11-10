module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcComp

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggFixedSubgroup {K : Type} [Group K] (E : Subgroup (MulAut K)) : Subgroup K where
  carrier := {k | ∀ ε ∈ E, ε k = k}
  one_mem' := fun ε _ => map_one ε
  mul_mem' := fun {a b} ha hb ε hε => by rw [map_mul, ha ε hε, hb ε hε]
  inv_mem' := fun {a} ha ε hε => by rw [map_inv, ha ε hε]

@[expose] def ggFixedClosure {K : Type} [Group K] (E : Subgroup (MulAut K)) : Subgroup K :=
  Subgroup.closure {k | ∃ ε ∈ E, ε ≠ 1 ∧ ε k = k}

section Transport

variable {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}


end Transport

section Comp

variable {W : Type} [Group W]

theorem ggSeitzExc_component_quot_equiv {H K C : Subgroup W}
    (hs : IsSimpleGroup ↥(commutator ↥(H.subgroupOf K)))
    (hns : ¬ Group.IsSolvable ↥(commutator ↥(H.subgroupOf K))) (hC : IsComponentOf C (H ⊓ K)) :
    Nonempty (↥C ⧸ Subgroup.center ↥C ≃* ↥(commutator ↥(H.subgroupOf K))) := by
  have hCeq := ggSeitzExc_component_eq hs hC
  let eC : ↥C ≃* ↥(commutator ↥(H.subgroupOf K)) :=
    (MulEquiv.subgroupCongr hCeq).trans (ggInfCommutatorEquiv H K)
  have : IsSimpleGroup ↥C := eC.isSimpleGroup
  have hCns : ¬ Group.IsSolvable ↥C := fun h' =>
    hns (Group.isSolvable_of_isSolvable_injective (f := eC.symm.toMonoidHom) eC.symm.injective)
  have hZ : Subgroup.center ↥C = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥C) with hc | hc
    · exact hc
    · refine absurd (Group.isSolvable_of_comm fun a b => ?_) hCns
      have hb : b ∈ Subgroup.center ↥C := hc ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eC⟩

end Comp

end CFSG.StandardType
