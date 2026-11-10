module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.GroupAction.ConjAct

public section

namespace CFSG.ComponentClassification.CatalogueBDerivedNormalSection

universe u v

variable {E : Type u} [Group E]

@[expose] def derivedNormalSubgroup (N : Subgroup E) : Subgroup E :=
  (commutator N).map N.subtype

theorem derivedNormalSubgroup_eq (N : Subgroup E) :
    derivedNormalSubgroup N = ⁅N, N⁆ :=
  N.map_subtype_commutator


instance derivedNormalSubgroupNormal (N : Subgroup E) [N.Normal] :
    (derivedNormalSubgroup N).Normal := by
  unfold derivedNormalSubgroup
  infer_instance

@[expose] def sectionDenominator (N Z : Subgroup E) :
    Subgroup (derivedNormalSubgroup N) :=
  Z.subgroupOf (derivedNormalSubgroup N)


instance sectionDenominatorNormal (N Z : Subgroup E) [Z.Normal] :
    (sectionDenominator N Z).Normal := by
  unfold sectionDenominator
  infer_instance


abbrev Section (N Z : Subgroup E) :=
  derivedNormalSubgroup N ⧸ sectionDenominator N Z

@[expose] def sectionProjection (N Z : Subgroup E) [Z.Normal] :
    derivedNormalSubgroup N →* Section N Z :=
  QuotientGroup.mk' (sectionDenominator N Z)

theorem sectionProjection_surjective (N Z : Subgroup E) [Z.Normal] :
    Function.Surjective (sectionProjection N Z) :=
  QuotientGroup.mk'_surjective (sectionDenominator N Z)


theorem derivedSeries_le_normal_of_quotient (N : Subgroup E) [N.Normal] (r : ℕ)
    (hquotient : derivedSeries (E ⧸ N) r = ⊥) :
    derivedSeries E r ≤ N := by
  have hmap : (derivedSeries E r).map (QuotientGroup.mk' N) = ⊥ := by
    rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective N) r, hquotient]
  simpa only [QuotientGroup.ker_mk'] using
    (Subgroup.map_eq_bot_iff (derivedSeries E r)).mp hmap

theorem derivedSeries_succ_le_derivedNormalSubgroup (N : Subgroup E) [N.Normal] (r : ℕ)
    (hquotient : derivedSeries (E ⧸ N) r = ⊥) :
    derivedSeries E (r + 1) ≤ derivedNormalSubgroup N := by
  rw [derivedSeries_succ, derivedNormalSubgroup_eq]
  exact Subgroup.commutator_mono
    (derivedSeries_le_normal_of_quotient N r hquotient)
    (derivedSeries_le_normal_of_quotient N r hquotient)

end CFSG.ComponentClassification.CatalogueBDerivedNormalSection
