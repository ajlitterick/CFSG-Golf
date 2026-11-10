module

public import CFSG.LocalAnalysis.ComponentClassification.ComponentFamilyPumpUpFusion
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.ThreePointCommutingActions
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationAction

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockThreeFactorImages

@[expose] noncomputable def image {G : Type*} [Group G] (normalizer factor : Subgroup G)
    (permutation : normalizer →* Equiv.Perm (Fin 3)) : Subgroup (Equiv.Perm (Fin 3)) :=
  (factor.subgroupOf normalizer).map permutation

theorem commute {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (normalizer : Subgroup G) (permutation : normalizer →* Equiv.Perm (Fin 3)) :
    Pairwise (fun first second : ↥(UniversalOrbitBlock.block component) =>
      ⁅image normalizer first.val permutation, image normalizer second.val permutation⁆ = ⊥) := by
  intro first second hne
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  rintro firstPermutation ⟨firstLift, hfirstLift, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  rintro secondPermutation ⟨secondLift, hsecondLift, rfl⟩
  rw [← map_mul, ← map_mul]
  apply congrArg permutation
  apply Subtype.ext
  have hcentral := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (UniversalOrbitBlock.block_commutes component heven huniversal first.val first.property second.val second.property
      (fun heq => hne (Subtype.ext heq)))
  exact Subgroup.mem_centralizer_iff.mp (hcentral hfirstLift) secondLift.val hsecondLift

theorem range_eq {G : Type*} [Group G] (normalizer factor : Subgroup G)
    (permutation : normalizer →* Equiv.Perm (Fin 3)) :
    let overlap := factor ⊓ normalizer
    let inclusion := Subgroup.inclusion (inf_le_right : overlap ≤ normalizer)
    (permutation.comp inclusion).range = image normalizer factor permutation := by
  ext member
  constructor
  · rintro ⟨lift, rfl⟩
    exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion inf_le_right lift, lift.property.1, rfl⟩
  · rintro ⟨lift, hlift, rfl⟩
    exact ⟨⟨lift.val, hlift, lift.property⟩, rfl⟩


end CFSG.ComponentClassification.BlockThreeFactorImages
