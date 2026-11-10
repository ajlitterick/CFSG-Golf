module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFour
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasThree

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}


theorem map_span_singleton_eq_iff {g : V ≃ₗ[K] V} {v : V} (hv : v ≠ 0) :
    (Submodule.span K {v}).map (g : V →ₗ[K] V) = Submodule.span K {v} ↔
      ∃ c : K, g v = c • v := by
  rw [Submodule.map_span, Set.image_singleton]
  constructor
  · intro h
    have hmem : g v ∈ Submodule.span K {v} := h ▸ Submodule.mem_span_singleton_self (g v)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul, LinearEquiv.map_eq_zero_iff] at hc
      exact hv hc
    change Submodule.span K {g v} = _
    rw [hc]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0) v

theorem orthogonal_singular_line_scalar_kernel [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 2 ∧ ∀ x ∈ T, Q x = 0) :
    (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ v : V, v ≠ 0 → Q v = 0 →
        (Submodule.span K {v}).map (g : V →ₗ[K] V) = Submodule.span K {v}) ↔
      g ∈ scalars K V) ∧
    ∀ A : Subgroup (V ≃ₗ[K] V), A ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      {g | g ∈ A ∧ ∀ v : V, v ≠ 0 → Q v = 0 →
        (Submodule.span K {v}).map (g : V →ₗ[K] V) = Submodule.span K {v}} =
        ((A ⊓ scalars K V : Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) := by
  obtain ⟨P₁, P₂, h⟩ := exists_orth_hypPairs_of_plane hQ hT
  have key : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ v : V, v ≠ 0 → Q v = 0 →
        (Submodule.span K {v}).map (g : V →ₗ[K] V) = Submodule.span K {v}) ↔
      g ∈ scalars K V := by
    intro g hg
    constructor
    · intro hfix
      exact mem_scalars_of_forall_singular h hg fun v hv hQv =>
        (map_span_singleton_eq_iff hv).1 (hfix v hv hQv)
    · intro hs v hv _
      obtain ⟨c, hc⟩ := (mem_scalars).1 hs
      exact (map_span_singleton_eq_iff hv).2 ⟨c, hc v⟩
  refine ⟨key, fun A hA => Set.ext fun g => ?_⟩
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_inf]
  exact ⟨fun ⟨hgA, hfix⟩ => ⟨hgA, (key g (hA hgA)).1 hfix⟩,
    fun ⟨hgA, hs⟩ => ⟨hgA, (key g (hA hgA)).2 hs⟩⟩

theorem orthogonal_char_two_projective_derived_simple [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P : ℕ → HypPair Q} {r : ℕ}
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)) (hr : 3 ≤ r)
    (hA : ∀ x ∈ tailSpace P r, Q x = 0 → x = 0)
    (hdim : finrank K (tailSpace P r) = 0 ∨ finrank K (tailSpace P r) = 2) :
    Nontrivial (↥(⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆) ⧸
      (scalars K V).subgroupOf ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆) ∧
    IsSimpleGroup (↥(⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆) ⧸
      (scalars K V).subgroupOf ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆) := by
  have hD := orthogonal_char_two_derived_elementary hQ hP hr hA hdim
  obtain ⟨T, hT3, hTs⟩ := exists_totallySingular_of_hypPairs (hP 0 1 (by omega) (by omega)
    (by omega)) (hP 0 2 (by omega) (by omega) (by omega)) (hP 1 2 (by omega) (by omega)
    (by omega))
  have hsimple : IsSimpleGroup (ProjElementary Q) :=
    isSimpleGroup_projElementary hQ (T := T) hT3.ge hTs
  rw [hD]
  exact ⟨hsimple.toNontrivial, hsimple⟩

end CFSG.LocalAnalysis.ComponentInitial
