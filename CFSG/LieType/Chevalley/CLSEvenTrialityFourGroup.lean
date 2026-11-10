module

public import CFSG.LieType.Chevalley.CLSEvenCoordinateFieldsFourGroup
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

@[expose] def d4TrialityHighestRoot : Fin TwistTag.D4.tag.rank → ℤ :=
  (![1, 1, 2, 1] : Fin 4 → ℤ)

@[expose] def d4CentralIndex : Fin TwistTag.D4.tag.rank :=
  ⟨2, by decide⟩

theorem isRoot_d4TrialityHighestRoot
    : IsRoot TwistTag.D4.tag d4TrialityHighestRoot :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨22, by decide, by decide⟩

theorem height_d4TrialityHighestRoot : height d4TrialityHighestRoot = 5 := by
  decide

theorem height_le_five_of_isRoot_D4 {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) : height α ≤ 5 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h : (List.range TwistTag.D4.tag.rootCertificate.roots.length).all fun k =>
      decide (height (TwistTag.D4.tag.rootCertificate.root k) ≤ 5) := by decide
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

theorem forall_height_le_d4TrialityHighestRoot :
    ∀ γ, IsRoot TwistTag.D4.tag γ → height γ ≤ height d4TrialityHighestRoot := fun _ hγ => by
  rw [height_d4TrialityHighestRoot]
  exact height_le_five_of_isRoot_D4 hγ

theorem permLattice_d4TrialityHighestRoot :
    permLattice TwistTag.D4.perm d4TrialityHighestRoot = d4TrialityHighestRoot := by
  decide

theorem perm_d4CentralIndex : TwistTag.D4.perm d4CentralIndex = d4CentralIndex := by
  decide

theorem twistHom_pinnedX_one_of_fixed
    {t : TwistTag} {K : Type} [Field K] (h2 : (2 : K) = 0)
    (σ : K →+* K) {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α)
    (hρ : permLattice t.perm α = α) :
    twistHom t K σ (pinnedX t.tag K α 1) = pinnedX t.tag K α 1 := by
  have hσ : Units.map (entrywiseHom σ) (pinnedX t.tag K α 1) = pinnedX t.tag K α 1 :=
    Units.ext (entrywise_pinnedX_one σ α)
  rw [twistHom_apply, hσ, ← twistHom_id_eq, twistHom_id_pinnedX h2 hα, hρ]

theorem pinnedX_one_mem_graphFixedRootGroup
    {t : TwistTag} {K : Type} [Field K]
    (h2 : (2 : K) = 0) (σ : K →+* K) {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α)
    (hpos : 0 < height α) (hρ : permLattice t.perm α = α) :
    pinnedX t.tag K α 1 ∈ graphFixedRootGroup t K σ :=
  Subgroup.mem_sup_left (Subgroup.mem_inf.2
    ⟨pinnedX_mem_rootSpan (S := {β | IsRoot t.tag β ∧ 0 < height β}) ⟨hα, hpos⟩ 1,
      pinnedX_mem_adjointGroup α 1, twistHom_pinnedX_one_of_fixed h2 σ hα hρ⟩)


end CFSG.LieType.Chevalley
