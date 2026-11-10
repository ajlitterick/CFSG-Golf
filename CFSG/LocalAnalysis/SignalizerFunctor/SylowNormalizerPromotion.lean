module

public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageAmbientNormalizers

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]


theorem pgroup_sylow_of_normalizer_pgroups (prime : ℕ) (prime_prime : prime.Prime)
    (target : Subgroup GroupType) (target_pgroup : IsPGroup prime target)
    (contains_pgroups : ∀ subgroup : Subgroup GroupType, IsPGroup prime subgroup →
      subgroup ≤ Subgroup.normalizer (target : Set GroupType) → subgroup ≤ target) :
    ∃ sylow : Sylow prime GroupType, (sylow : Subgroup GroupType) = target := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  obtain ⟨sylow, target_le⟩ := target_pgroup.exists_le_sylow
  let internal := target.subgroupOf (sylow : Subgroup GroupType)
  let _nilpotent : Group.IsNilpotent (sylow : Subgroup GroupType) := sylow.isPGroup'.isNilpotent
  have normalizer_le : Subgroup.normalizer (internal : Set (sylow : Subgroup GroupType)) ≤ internal := by
    let normalizer := Subgroup.normalizer (internal : Set (sylow : Subgroup GroupType))
    let embedded := normalizer.map (sylow : Subgroup GroupType).subtype
    have embedded_pgroup : IsPGroup prime embedded :=
      (sylow.isPGroup'.to_subgroup normalizer).map (sylow : Subgroup GroupType).subtype
    have normalized : embedded ≤ Subgroup.normalizer (target : Set GroupType) := by
      have formula := normalizer_subtype_map (sylow : Subgroup GroupType) internal
      rw [Subgroup.map_subgroupOf_eq_of_le target_le] at formula
      change normalizer.map (sylow : Subgroup GroupType).subtype ≤ _
      rw [formula]
      exact inf_le_right
    have contained := contains_pgroups embedded embedded_pgroup normalized
    intro element member
    exact contained (Subgroup.mem_map_of_mem (sylow : Subgroup GroupType).subtype member)
  have equal : internal = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := (sylow : Subgroup GroupType)))) internal
      (le_antisymm normalizer_le Subgroup.le_normalizer)
  have mapped_eq := congrArg (Subgroup.map (sylow : Subgroup GroupType).subtype) equal
  rw [Subgroup.map_subgroupOf_eq_of_le target_le, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at mapped_eq
  exact ⟨sylow, mapped_eq.symm⟩

omit [Finite GroupType] in
theorem parent_sylow_normalizer_pgroup_le (prime : ℕ) (parent : Subgroup GroupType)
    (sylow : Sylow prime parent) (target : Subgroup GroupType) (target_le : target ≤ parent)
    (target_pgroup : IsPGroup prime target)
    (normalized : target ≤ Subgroup.normalizer
      (((sylow : Subgroup parent).map parent.subtype : Subgroup GroupType) : Set GroupType)) :
    target ≤ (sylow : Subgroup parent).map parent.subtype := by
  let internal := target.subgroupOf parent
  have internal_pgroup : IsPGroup prime internal :=
    target_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe target_le).symm
  have internal_normalized : internal ≤ Subgroup.normalizer (sylow : Set parent) := by
    have mapped_formula := normalizer_subtype_map parent (sylow : Subgroup parent)
    apply Subgroup.map_subtype_le_map_subtype.mp
    change internal.map parent.subtype ≤
      (Subgroup.normalizer ((sylow : Subgroup parent) : Set parent)).map parent.subtype
    rw [mapped_formula, Subgroup.map_subgroupOf_eq_of_le target_le]
    exact le_inf target_le normalized
  have formula := internal_pgroup.inf_normalizer_sylow sylow
  rw [inf_eq_left.mpr internal_normalized] at formula
  have internal_le : internal ≤ (sylow : Subgroup parent) := formula.le.trans inf_le_right
  have mapped_le := Subgroup.map_mono (f := parent.subtype) internal_le
  rwa [Subgroup.map_subgroupOf_eq_of_le target_le] at mapped_le

end CFSG.SignalizerFunctor.Helpers
