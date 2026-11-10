module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Blocks
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.OrbitCongruence
public import Mathlib.Tactic.Polynomial.Basic

public section

open CFSG
open scoped Classical

namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem centralizer_conj_mem {G : Type*} [Group G] (subgroup : Subgroup G)
    {element conjugator : G} (hconjugator : conjugator ∈ Subgroup.normalizer (subgroup : Set G))
    (helement : element ∈ Subgroup.centralizer (subgroup : Set G)) :
    conjugator * element * conjugator⁻¹ ∈ Subgroup.centralizer (subgroup : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at helement ⊢
  intro member hmember
  have hinverse := (Subgroup.mem_normalizer_iff''.mp hconjugator member).mp hmember
  have hcommute := helement (conjugator⁻¹ * member * conjugator) hinverse
  have hconjugated := congrArg (fun value : G => conjugator * value * conjugator⁻¹) hcommute
  convert hconjugated using 1 <;> group

theorem centralizer_conj_iff {G : Type*} [Group G] (subgroup : Subgroup G)
    {element conjugator : G} (hconjugator : conjugator ∈ Subgroup.normalizer (subgroup : Set G)) :
    conjugator * element * conjugator⁻¹ ∈ Subgroup.centralizer (subgroup : Set G) ↔
      element ∈ Subgroup.centralizer (subgroup : Set G) := by
  constructor
  · intro hconjugated
    have hinverse := centralizer_conj_mem subgroup
      ((Subgroup.normalizer (subgroup : Set G)).inv_mem hconjugator) hconjugated
    have hequal : conjugator⁻¹ * (conjugator * element * conjugator⁻¹) * conjugator =
        element := by group
    rwa [inv_inv, hequal] at hinverse
  · exact centralizer_conj_mem subgroup hconjugator

theorem brauerProj_apply {G : Type*} [Group G] (subgroup overgroup : Subgroup G)
    (value : G → ℂ) (element : overgroup) :
    BlocksBrauerProj subgroup overgroup value element =
      if (element : G) ∈ Subgroup.centralizer (subgroup : Set G) then value element else 0 := by
  classical
  simp only [BlocksBrauerProj, Set.indicator_apply, Set.mem_ofPred_eq]

theorem brauerProj_central {G : Type*} [Group G] (m : Ideal BlocksAlgInt)
    (hm : m.IsMaximal) (subgroup overgroup : Subgroup G)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    {value : G → ℂ} (hvalue : BlocksIsCentralR m value) :
    BlocksIsCentralR m (BlocksBrauerProj subgroup overgroup value) := by
  classical
  constructor
  · intro element
    rw [brauerProj_apply]
    split_ifs
    · exact hvalue.1 element
    · exact localRing_zero m hm
  · intro element conjugator
    simp only [brauerProj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [centralizer_conj_iff subgroup (hnormalizer conjugator.property), hvalue.2]


end CFSG.BrauerThirdMainTheorem.Helpers
