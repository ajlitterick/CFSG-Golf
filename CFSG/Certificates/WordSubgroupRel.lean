module

public import CFSG.Certificates.WordSubgroup

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}


theorem exists_hom_range (ws hs : List (List (Fin m × Bool)))
    (R : List (List (Fin hs.length × Bool)))
    (hR : ∀ u ∈ R.map (substWord hs),
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u) = 1) :
    ∃ π : PG hs.length R →* PG m ws,
      π.range = Subgroup.closure
        {g | ∃ s ∈ hs, g = PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
          (FreeGroup.mk s)} := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set H : Subgroup (PG m ws) :=
    Subgroup.closure {g | ∃ s ∈ hs, g = PresentedGroup.mk rels (FreeGroup.mk s)}
  set f : Fin hs.length → PG m ws :=
    fun i => PresentedGroup.mk rels (FreeGroup.mk (hs.getD i []))
  have hf : ∀ r ∈ {r : FreeGroup (Fin hs.length) | r ∈ R.map FreeGroup.mk},
      FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_substWord]
    exact hR _ (List.mem_map_of_mem hw)
  refine ⟨PresentedGroup.toGroup hf, ?_⟩
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    induction g using PresentedGroup.induction_on with
    | H x =>
      induction x using FreeGroup.induction_on with
      | one => simp
      | of i =>
        show PresentedGroup.toGroup hf (PresentedGroup.of i) ∈ H
        rw [PresentedGroup.toGroup.of]
        exact Subgroup.subset_closure
          ⟨_, by rw [List.getD_eq_getElem _ _ i.isLt]; exact List.getElem_mem _, rfl⟩
      | inv_of i hi =>
        rw [map_inv, map_inv]
        exact H.inv_mem hi
      | mul x y hx hy =>
        rw [map_mul, map_mul]
        exact H.mul_mem hx hy
  · rw [Subgroup.closure_le]
    rintro _ ⟨s, hs', rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs'
    refine ⟨PresentedGroup.of ⟨i, hi⟩, ?_⟩
    rw [PresentedGroup.toGroup.of]
    simp only [f, List.getD_eq_getElem _ _ hi]


end CFSG.CosetTable
