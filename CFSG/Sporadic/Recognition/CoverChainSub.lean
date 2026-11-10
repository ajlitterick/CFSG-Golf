module

public import CFSG.Sporadic.Recognition.CoverRecipeSq

public section

namespace CFSG.Sporadic.Recognition.CoverRecipe

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverTransfer

variable {m : ℕ}

theorem mem_cover₂Words_of_subset {R R' : List (List (Fin m × Bool))}
    (hR : ∀ r ∈ R, r ∈ R') {cw : Fin m → List (Fin m × Bool)} {w : List (Fin m × Bool)}
    (hw : w ∈ cover₂Words R cw) : w ∈ cover₂Words R' cw := by
  rw [mem_cover₂Words] at hw ⊢
  simp only [coverWords, squareWords, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hw ⊢
  rcases hw with (⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩) | ⟨r, hr, rfl⟩
  · exact Or.inl (Or.inl ⟨i, r, hR r hr, rfl⟩)
  · exact Or.inl (Or.inr ⟨i, rfl⟩)
  · exact Or.inr ⟨r, hR r hr, rfl⟩

theorem mem_restrictWords_of_subset {S : List (Fin m)} {ws ws' : List (List (Fin m × Bool))}
    (h : ∀ w ∈ ws, w ∈ ws') {w : List (Fin S.length × Bool)} (hw : w ∈ restrictWords S ws) :
    w ∈ restrictWords S ws' := by
  simp only [restrictWords, List.mem_filterMap] at hw ⊢
  obtain ⟨v, hv, hvw⟩ := hw
  exact ⟨v, h v hv, hvw⟩

theorem exists_surjective_PG {ws₀ ws : List (List (Fin m × Bool))} (h : ∀ w ∈ ws₀, w ∈ ws) :
    ∃ π : PG m ws₀ →* PG m ws, Function.Surjective π ∧
      ∀ i, π (PresentedGroup.of i) = PresentedGroup.of i := by
  have hrel : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws₀.map FreeGroup.mk},
      FreeGroup.lift (PresentedGroup.of : Fin m → PG m ws) r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [← mk_eq_lift_of]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (h w hw))
  refine ⟨PresentedGroup.toGroup hrel, ?_, fun i => PresentedGroup.toGroup.of hrel⟩
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of hrel⟩


end CFSG.Sporadic.Recognition.CoverRecipe
