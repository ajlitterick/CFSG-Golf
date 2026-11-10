module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionLayer

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

open CFSG.Open

variable {G : Type*} [Group G]


variable [Finite G]


theorem perfect_layer_centralizer_product_absorption (K : Subgroup G)
    [Group.IsPerfect K]
    (hproduct : K ≤ Layer.subgroup G ⊔ Subgroup.centralizer (Layer.subgroup G : Set G))
    (hKF : ⁅K, Fitting.subgroup G⁆ = ⊥) : K ≤ Layer.subgroup G := by
  let E := Layer.subgroup G
  let F := Fitting.subgroup G
  let : E.Normal := Layer.normal G
  let : F.Normal := Fitting.normal G
  let : Group.IsSolvable F := Fitting.solvable G
  have hEF : E ≤ Subgroup.centralizer (F : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact GeneralizedFitting.fitting_layer_commute G)
  have hKG : K ≤ GeneralizedFitting.subgroup G := by
    intro k hk
    obtain ⟨e, he, c, hc, hec⟩ := Subgroup.mem_sup_of_normal_left.mp (hproduct hk)
    have hcF : c ∈ Subgroup.centralizer (F : Set G) := by
      have hmem := (Subgroup.centralizer (F : Set G)).mul_mem
        ((Subgroup.centralizer (F : Set G)).inv_mem (hEF he))
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKF hk)
      rw [← hec] at hmem
      simpa only [inv_mul_cancel_left] using hmem
    have hcGeneralized : c ∈ Subgroup.centralizer (GeneralizedFitting.subgroup G : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      have hbound : F ⊔ E ≤ Subgroup.centralizer ({c} : Set G) := by
        apply sup_le
        · intro f hf
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hcF f hf)
        · intro e he
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hc e he)
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hbound hx)
    have hcFit := GeneralizedFitting.centralizer_le_fitting G hcGeneralized
    rw [← hec]
    exact (GeneralizedFitting.subgroup G).mul_mem
      ((le_sup_right : E ≤ GeneralizedFitting.subgroup G) he)
      ((le_sup_left : F ≤ GeneralizedFitting.subgroup G) hcFit)
  let q := QuotientGroup.mk' F
  let : Group.IsSolvable q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    infer_instance
  apply SolvableKernelContainment.perfect_containment q K E
  have hmap := Subgroup.map_mono (f := q) hKG
  change K.map q ≤ (F ⊔ E).map q at hmap
  rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at hmap

end CFSG.ComponentClassification.AschbacherComponentInvolution
