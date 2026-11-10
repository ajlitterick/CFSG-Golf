module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.BinaryRank
public import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalCentralizer
public import CFSG.LocalAnalysis.PreuniquenessRankFour.BinaryUnits

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem binary_module_finrank_le_group_rank
    {source : Type u} [CommGroup source] [Finite source]
    [Module (ZMod 2) (Additive source)] :
    Module.finrank (ZMod 2) (Additive source) ≤ Group.rank source := by
  classical
  obtain ⟨generators, hcard, hgeneration⟩ := Group.rank_spec source
  let vectors := generators.image (Additive.ofMul : source → Additive source)
  let span := Submodule.span (ZMod 2) (vectors : Set (Additive source))
  have hclosure : Subgroup.closure (generators : Set source) ≤ span.toAddSubgroup.toSubgroup' := by
    apply (Subgroup.closure_le _).mpr
    intro member hmember
    change Additive.ofMul member ∈ span
    exact Submodule.subset_span (Finset.mem_image_of_mem _ hmember)
  have hspan : span = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro member
    exact hclosure (hgeneration ▸ Subgroup.mem_top member.toMul)
  have hdimension := finrank_span_finset_le_card (R := ZMod 2) vectors
  change Module.finrank (ZMod 2) span ≤ vectors.card at hdimension
  rw [hspan, finrank_top] at hdimension
  exact hdimension.trans (Finset.card_image_le.trans hcard.le)

theorem binary_module_group_rank_le_finrank
    {source : Type u} [CommGroup source] [Finite source]
    [Module (ZMod 2) (Additive source)] :
    Group.rank source ≤ Module.finrank (ZMod 2) (Additive source) := by
  classical
  let basis := Module.finBasis (ZMod 2) (Additive source)
  let generators := Finset.univ.image (fun index => (basis index).toMul)
  let generated := Subgroup.closure (generators : Set source)
  let submodule := (AddSubgroup.toZModSubmodule 2) generated.toAddSubgroup
  have hbasis : Submodule.span (ZMod 2) (Set.range basis) ≤ submodule := by
    apply Submodule.span_le.mpr
    rintro member ⟨index, rfl⟩
    change (basis index).toMul ∈ generated
    apply Subgroup.subset_closure
    exact Finset.mem_image_of_mem _ (Finset.mem_univ index)
  have hgenerated : generated = ⊤ := by
    apply top_unique
    intro member _
    have hspan : Additive.ofMul member ∈ Submodule.span (ZMod 2) (Set.range basis) :=
      basis.span_eq ▸ Submodule.mem_top
    have hmem := hbasis hspan
    change Additive.ofMul member ∈ submodule.toAddSubgroup at hmem
    rw [AddSubgroup.toZModSubmodule_toAddSubgroup] at hmem
    exact hmem
  exact (Group.rank_le (S := generators) hgenerated).trans
    (Finset.card_image_le.trans (by simp))

theorem binary_module_group_rank_eq_finrank
    {source : Type u} [CommGroup source] [Finite source]
    [Module (ZMod 2) (Additive source)] :
    Group.rank source = Module.finrank (ZMod 2) (Additive source) :=
  le_antisymm binary_module_group_rank_le_finrank binary_module_finrank_le_group_rank

theorem twoGroup_frattini_finrank_eq_group_rank
    {source : Type u} [Group source] [Finite source] (hsource : IsPGroup 2 source) :
    letI : IsMulCommutative (source ⧸ frattini source) :=
      pGroup_frattini_quotient_isMulCommutative 2 hsource
    letI : CommGroup (source ⧸ frattini source) := IsMulCommutative.instCommGroup
    letI := pGroup_binary_frattini_quotient_module hsource
    Module.finrank (ZMod 2) (Additive (source ⧸ frattini source)) = Group.rank source := by
  classical
  let : IsMulCommutative (source ⧸ frattini source) :=
    pGroup_frattini_quotient_isMulCommutative 2 hsource
  let : CommGroup (source ⧸ frattini source) := IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module hsource
  apply le_antisymm
  · exact binary_module_finrank_le_group_rank.trans
      (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini source))
        (QuotientGroup.mk'_surjective (frattini source)))
  · obtain ⟨quotientGenerators, hcard, hgeneration⟩ := Group.rank_spec (source ⧸ frattini source)
    let lift : (source ⧸ frattini source) → source :=
      fun member => Classical.choose (QuotientGroup.mk'_surjective (frattini source) member)
    have hlift : ∀ member, (QuotientGroup.mk' (frattini source)) (lift member) = member :=
      fun member => Classical.choose_spec (QuotientGroup.mk'_surjective (frattini source) member)
    let generators := quotientGenerators.image lift
    let generated := Subgroup.closure (generators : Set source)
    have hquotient : generated.map (QuotientGroup.mk' (frattini source)) = ⊤ := by
      apply top_unique
      rw [← hgeneration]
      apply (Subgroup.closure_le _).mpr
      intro member hmember
      exact ⟨lift member, Subgroup.subset_closure (Finset.mem_image_of_mem _ hmember), hlift member⟩
    have hjoin : generated ⊔ frattini source = ⊤ := by
      rw [← QuotientGroup.ker_mk' (frattini source), ← Subgroup.comap_map_eq, hquotient,
        Subgroup.comap_top]
    have hgenerated : generated = ⊤ := frattini_nongenerating hjoin
    exact (Group.rank_le (S := generators) hgenerated).trans
      (Finset.card_image_le.trans (hcard.le.trans binary_module_group_rank_le_finrank))


end CFSG.PreuniquenessRankFour.Helpers
