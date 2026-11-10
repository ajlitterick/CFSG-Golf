module

public import CFSG.Quasithin.Background.RonanH163Base
public import CFSG.Quasithin.Background.RonanH163Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf


theorem mem_stabSub_of_forward {V : Type*} [CommGroup V] [Finite V] {U : Subgroup V}
    {g : MulAut V} (h : ∀ u ∈ U, g u ∈ U) : g ∈ stabSub U := by
  refine mem_stabSub.2 fun v => ⟨fun hv => ?_, h v⟩
  have hf : Function.Injective (fun u : U => (⟨g u, h u u.2⟩ : U)) := fun a b hab =>
    Subtype.ext (g.injective (congrArg Subtype.val hab))
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective hf ⟨g v, hv⟩
  have hgv : g u = g v := congrArg Subtype.val hu
  rw [← g.injective hgv]
  exact u.2


theorem g1Perm_mem_gen :
    g1Perm ∈ Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) :=
  Subgroup.subset_closure (Or.inr (Set.mem_insert _ _))

theorem g2Perm_mem_gen :
    g2Perm ∈ Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) :=
  Subgroup.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem nq2_le_gen : NQ2 ≤ Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) :=
  fun _ hx => Subgroup.subset_closure (Or.inl hx)


theorem MQ_le_closure :
    MY mog22plus Qstd ≤ Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) := by
  set H : Subgroup P24 := Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) with hH
  set H' : Subgroup ↥(MY mog22plus Qstd) := H.subgroupOf (MY mog22plus Qstd) with hH'
  have hg1 : (⟨g1Perm, g1Perm_mem_MY g1Perm_mem_mog22plus⟩ : ↥(MY mog22plus Qstd)) ∈ H' :=
    Subgroup.mem_subgroupOf.2 g1Perm_mem_gen
  have hg2 : (⟨g2Perm, g2Perm_mem_MY g2Perm_mem_mog22plus⟩ : ↥(MY mog22plus Qstd)) ∈ H' :=
    Subgroup.mem_subgroupOf.2 g2Perm_mem_gen
  have hm := map_closure_eq_top_of_cycle_swap (piQ mog22plus) sig1 sig1_isCycle sig1_support 3
    ⟨g1Perm, g1Perm_mem_MY g1Perm_mem_mog22plus⟩ ⟨g2Perm, g2Perm_mem_MY g2Perm_mem_mog22plus⟩
    (piQ_eq_of_smul _ _ g1_smul_Zq) (by rw [← sig2_eq]; exact piQ_eq_of_smul _ _ g2_smul_Zq)
  have hsig : H'.map (piQ mog22plus) = ⊤ := by
    rw [eq_top_iff, ← hm]
    apply Subgroup.map_mono
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hg1
    · exact hg2
  intro g hg
  have h1 : piQ mog22plus ⟨g, hg⟩ ∈ H'.map (piQ mog22plus) := by
    rw [hsig]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, hgh⟩ := h1
  have h2 : (⟨g, hg⟩ : ↥(MY mog22plus Qstd)) * h⁻¹ ∈ (piQ mog22plus).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, mul_inv_cancel]
  rw [ker_piQ_L2, Subgroup.mem_subgroupOf] at h2
  have h3 : g * (h : P24)⁻¹ ∈ H := nq2_le_gen h2
  have h4 : (h : P24) ∈ H := Subgroup.mem_subgroupOf.1 hh
  simpa using H.mul_mem h3 h4


end CFSG.Quasithin.RonanH163
