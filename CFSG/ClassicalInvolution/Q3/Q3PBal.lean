module

public import CFSG.ClassicalInvolution.Q3.Q3PlanQS3

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification


section Centralizes

variable {X : Type} [Group X] [Finite X] {z : X} {L : Subgroup X}

theorem IsClassicalMember3.le_centralizer_of_le_centralizer (hL : IsClassicalMember3 L z)
    {T : Subgroup X} (hT : IsComponentOf T ⊤) (hTz : T ≤ Subgroup.centralizer ({z} : Set X)) :
    L ≤ Subgroup.centralizer (T : Set X) := by
  set C : Subgroup X := Subgroup.centralizer ({z} : Set X) with hC
  have hLC : L ≤ C := isSubnormal_le hL.subnormal
  have hTC : IsComponentOf (T.subgroupOf C) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have h := isSubnormal_subgroupOf hT.2.1 C
      rwa [Subgroup.top_subgroupOf] at h
    · exact Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hTz) hT.2.2
  have hLsub : IsSubnormal (L.subgroupOf C) ⊤ := by
    have h := isSubnormal_subgroupOf hL.subnormal C
    rwa [Subgroup.subgroupOf_self] at h
  have hsolv : Group.IsSolvable (L.subgroupOf C) :=
    have := hL.isSolvable
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hLC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLC).injective
  have hcomm := @Layer.commutes_with_solvable_subnormal C _ _ (L.subgroupOf C) hLsub hsolv
  have hle : T.subgroupOf C ≤ Layer.subgroup C := Layer.component_le hTC
  have hcent : Layer.subgroup C ≤ Subgroup.centralizer ((L.subgroupOf C : Subgroup C) : Set C) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 : (⟨t, hTz ht⟩ : C) ∈ Subgroup.centralizer ((L.subgroupOf C : Subgroup C) : Set C) :=
    hcent (hle ht)
  have h2 := Subgroup.mem_centralizer_iff.mp h1 (⟨l, hLC hl⟩ : C) hl
  exact (congrArg Subtype.val h2).symm

end Centralizes


end CFSG.ClassicalInvolution.Q3
