module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Group

variable {G : Type} [Group G]

theorem ggEq_of_isSubnormal_of_isSimpleGroup {C M : Subgroup G}
    (h : CFSG.Assembly.IsSubnormal C M) (hM : IsSimpleGroup ↥M) (hC : C ≠ ⊥) : C = M := by
  induction h with
  | refl => rfl
  | @step A B M hAB hn _ ih =>
    have hB : B = M := ih hM fun hB => hC (le_bot_iff.mp (hB ▸ hAB))
    subst hB
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hM _ hn with h | h
    · exfalso
      apply hC
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact le_bot_iff.mp fun x hx => (Subgroup.disjoint_def.mp h) hx (hAB hx) ▸ Subgroup.mem_bot.mpr rfl
    · exact le_antisymm hAB (Subgroup.subgroupOf_eq_top.mp h)

theorem ggCommutator_subgroupOf (A : Subgroup G) : (⁅A, A⁆ : Subgroup G).subgroupOf A =
    commutator ↥A := by
  have hmap : (commutator ↥A).map A.subtype = ⁅A, A⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hmap, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective A.subtype_injective]

@[expose] noncomputable def ggCommutatorEquiv (A : Subgroup G) :
    ↥(⁅A, A⁆ : Subgroup G) ≃* ↥(commutator ↥A) :=
  ((Subgroup.equivMapOfInjective (commutator ↥A) A.subtype A.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]))).symm

theorem ggComponent_eq_commutator {A C : Subgroup G} (hC : IsComponentOf C A)
    (hs : IsSimpleGroup ↥(⁅A, A⁆ : Subgroup G)) : C = ⁅A, A⁆ := by
  have hCA : C ≤ ⁅A, A⁆ := by
    rw [← ggComponent_perfect hC]
    exact Subgroup.commutator_mono hC.1 hC.1
  have hsub := ggIsSubnormal_inf hC.2.1 ⁅A, A⁆
  have hAA : (⁅A, A⁆ : Subgroup G) ≤ A := Subgroup.commutator_le.mpr fun a ha b hb =>
    A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
  rw [inf_eq_left.mpr hCA, inf_eq_right.mpr hAA] at hsub
  exact ggEq_of_isSubnormal_of_isSimpleGroup hsub hs (ggComponent_ne_bot hC)

theorem ggMap_commutator_of_surjective {G' : Type} [Group G'] (f : G →* G')
    (hf : Function.Surjective f) : (commutator G).map f = commutator G' := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr hf]

@[expose] noncomputable def ggCommutatorCongr {G' : Type} [Group G'] (φ : G ≃* G') :
    ↥(commutator G) ≃* ↥(commutator G') :=
  (Subgroup.equivMapOfInjective (commutator G) φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (ggMap_commutator_of_surjective φ.toMonoidHom φ.surjective))

theorem ggIsSolvable_of_commutator (h : Group.IsSolvable ↥(commutator G)) : Group.IsSolvable G :=
  (Group.isSolvable_commutator_iff (G := G)).mp h

end Group

section Hyp

variable {W : Type} [Group W]

@[expose] noncomputable def ggSubgroupOfEquivInf (H K : Subgroup W) :
    ↥(H.subgroupOf K) ≃* ↥(H ⊓ K) :=
  (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right H K).symm).trans
    (Subgroup.subgroupOfEquivOfLe inf_le_right)

@[expose] noncomputable def ggInfCommutatorEquiv (H K : Subgroup W) :
    ↥(⁅H ⊓ K, H ⊓ K⁆ : Subgroup W) ≃* ↥(commutator ↥(H.subgroupOf K)) :=
  (ggCommutatorEquiv (H ⊓ K)).trans (ggCommutatorCongr (ggSubgroupOfEquivInf H K).symm)

theorem ggSeitzExc_component_eq {H K C : Subgroup W}
    (hs : IsSimpleGroup ↥(commutator ↥(H.subgroupOf K))) (hC : IsComponentOf C (H ⊓ K)) :
    C = ⁅H ⊓ K, H ⊓ K⁆ :=
  ggComponent_eq_commutator hC (ggInfCommutatorEquiv H K).isSimpleGroup


end Hyp

end CFSG.StandardType
