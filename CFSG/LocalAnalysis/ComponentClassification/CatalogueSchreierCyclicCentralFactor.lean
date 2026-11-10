module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierCyclicCentralFactorOuter
public import CFSG.LocalAnalysis.ComponentClassification.CenterlessCommutingFamily

public section

namespace CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor

open OuterAutomorphisms

variable {H : Type*} [Group H]

theorem central_factor_centralizes (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) : Z ≤ Subgroup.centralizer (L : Set H) := by
  intro member hmember
  apply Subgroup.mem_centralizer_iff.mpr
  intro other _
  exact Subgroup.mem_center_iff.mp (hcentral hmember) other

theorem internal_factor_normal (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) (hcover : L ⊔ Z = ⊤) : L.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hcover]
  exact sup_le Subgroup.le_normalizer
    ((central_factor_centralizes L Z hcentral).trans (Subgroup.centralizer_le_normalizer _))

theorem internal_factors_disjoint (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥) :
    Disjoint L Z :=
  CenterlessCommutingFamily.disjoint_of_centralizes L Z hcenter
    (central_factor_centralizes L Z hcentral)

@[expose] def internalMultiplication (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) : L × Z →* H :=
  L.subtype.noncommCoprod Z.subtype
    (fun left right => Subgroup.mem_center_iff.mp (hcentral right.property) left)

theorem internalMultiplication_injective (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥) :
    Function.Injective (internalMultiplication L Z hcentral) :=
  Subgroup.mul_injective_of_disjoint (internal_factors_disjoint L Z hcentral hcenter)

theorem internalMultiplication_surjective (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) (hcover : L ⊔ Z = ⊤) :
    Function.Surjective (internalMultiplication L Z hcentral) := by
  let : L.Normal := internal_factor_normal L Z hcentral hcover
  intro member
  have hmember : member ∈ L ⊔ Z := hcover.symm ▸ Subgroup.mem_top member
  obtain ⟨left, hleft, right, hright, heq⟩ := Subgroup.mem_sup_of_normal_left.mp hmember
  exact ⟨(⟨left, hleft⟩, ⟨right, hright⟩), heq⟩

@[expose] noncomputable def internalEquivalence (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥)
    (hcover : L ⊔ Z = ⊤) : L × Z ≃* H :=
  MulEquiv.ofBijective (internalMultiplication L Z hcentral)
    ⟨internalMultiplication_injective L Z hcentral hcenter,
      internalMultiplication_surjective L Z hcentral hcover⟩


theorem internal_outer_solvable (L Z : Subgroup H) [Group.IsPerfect L] [IsCyclic Z]
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥)
    (hcover : L ⊔ Z = ⊤) [Group.IsSolvable (Outer L)] :
    Group.IsSolvable (Outer H) := by
  let : Group.IsSolvable (Outer (L × Z)) := outer_solvable_of_cyclic hcenter
  exact solvable_of_equiv (internalEquivalence L Z hcentral hcenter hcover)

end CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor
