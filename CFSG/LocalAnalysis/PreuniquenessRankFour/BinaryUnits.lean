module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v


theorem cyclic_group_rank_at_most_one
    {source : Type u} [Group source] [Finite source] [IsCyclic source] :
    Group.rank source ≤ 1 := by
  classical
  obtain ⟨generator, hgenerator⟩ := IsCyclic.exists_generator (α := source)
  have hclosure : Subgroup.closure ({generator} : Set source) = ⊤ := by
    rw [← Subgroup.zpowers_eq_closure]
    exact top_unique fun member _ => hgenerator member
  have hclosureFinset : Subgroup.closure (({generator} : Finset source) : Set source) = ⊤ := by
    simpa only [Finset.coe_singleton] using hclosure
  simpa only [Finset.card_singleton] using
    (Group.rank_le (S := {generator}) hclosureFinset)

theorem subgroup_rank_le_rank_add_quotient_rank
    {source : Type u} [Group source] [Finite source]
    (normal : Subgroup source) [normal.Normal] :
    Group.rank source ≤ Group.rank normal + Group.rank (source ⧸ normal) := by
  classical
  obtain ⟨normalGenerators, hnormalCard, hnormalGeneration⟩ := Group.rank_spec normal
  obtain ⟨quotientGenerators, hquotientCard, hquotientGeneration⟩ := Group.rank_spec (source ⧸ normal)
  let lift : (source ⧸ normal) → source :=
    fun member => Classical.choose (QuotientGroup.mk'_surjective normal member)
  have hlift : ∀ member, (QuotientGroup.mk' normal) (lift member) = member :=
    fun member => Classical.choose_spec (QuotientGroup.mk'_surjective normal member)
  let generators := normalGenerators.image normal.subtype ∪ quotientGenerators.image lift
  let generated := Subgroup.closure (generators : Set source)
  have hnormal : normal ≤ generated := by
    have hcomap : (⊤ : Subgroup normal) ≤ generated.comap normal.subtype := by
      rw [← hnormalGeneration]
      apply (Subgroup.closure_le _).mpr
      intro member hmember
      apply Subgroup.subset_closure
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmember)
    intro member hmember
    exact hcomap (Subgroup.mem_top (⟨member, hmember⟩ : normal))
  have hquotient : generated.map (QuotientGroup.mk' normal) = ⊤ := by
    apply top_unique
    rw [← hquotientGeneration]
    apply (Subgroup.closure_le _).mpr
    intro member hmember
    refine ⟨lift member, ?_, hlift member⟩
    apply Subgroup.subset_closure
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hmember)
  have hgenerated : generated = ⊤ := by
    apply top_unique
    intro member _
    obtain ⟨representative, hrepresentative, hequal⟩ :=
      (show (QuotientGroup.mk' normal) member ∈ generated.map (QuotientGroup.mk' normal) from
        hquotient ▸ Subgroup.mem_top _)
    have hdifference : representative⁻¹ * member ∈ normal := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' normal) (representative⁻¹ * member) = 1
      rw [map_mul, map_inv, hequal, inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using generated.mul_mem hrepresentative (hnormal hdifference)
  apply (Group.rank_le (S := generators) hgenerated).trans
  apply (Finset.card_union_le _ _).trans
  exact (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)).trans
    (le_of_eq (congrArg₂ (· + ·) hnormalCard hquotientCard))


end CFSG.PreuniquenessRankFour.Helpers
