module

public import CFSG.LocalAnalysis.ComponentClassification.MinimalBSolvable
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCyclicActions

public section

open CFSG.Open

namespace CFSG.ComponentClassification.MinimalBOddWitness

theorem exists_component {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (twoSubgroup : Subgroup G) (hne : twoSubgroup ≠ ⊥) (htwo : IsPGroup 2 twoSubgroup)
    (hfailure : ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
      (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤ TwoComponents.badSubgroup G)
    (solvableNormal : Subgroup G) [solvableNormal.Normal] [Group.IsSolvable solvableNormal]
    (hsolvableNe : solvableNormal ≠ ⊥) :
    ∃ (normalSubgroup : Subgroup G) (hnormal : normalSubgroup.Normal),
      letI : normalSubgroup.Normal := hnormal
      normalSubgroup ≤ solvableNormal ∧
      MinimalNormal.Property normalSubgroup ∧ normalSubgroup.Characteristic ∧
      Group.IsSolvable normalSubgroup ∧ Odd (Nat.card normalSubgroup) ∧
      ∃ component : Subgroup G,
        component ≤ Subgroup.normalizer (twoSubgroup : Set G) ∧
        TwoComponents.IsTwoComponent
          (component.subgroupOf (Subgroup.normalizer (twoSubgroup : Set G))) ∧
        Group.IsPerfect component ∧ ¬ IsQuasisimple component ∧
        ¬ component ≤ TwoComponents.badSubgroup G ∧
        component ≤ Subgroup.centralizer (twoSubgroup : Set G) ∧
        IsQuasisimple (component.map (QuotientGroup.mk' normalSubgroup)) ∧
        ¬ normalSubgroup.subgroupOf component ≤ Subgroup.center component := by
  have hglobalFailure : ¬ CentralTwoBInclusion.Property G :=
    fun hB => hfailure (hB twoSubgroup hne htwo)
  obtain ⟨normalSubgroup, hle, hminimal, hsolvable, hcharacteristic, _⟩ :=
    MinimalBSolvable.exists_characteristic_le hsmaller hproper hglobalFailure
      solvableNormal hsolvableNe
  let : Group.IsSolvable normalSubgroup := hsolvable
  let : normalSubgroup.Characteristic := hcharacteristic
  have hodd := MinimalBSolvable.odd_card hsmaller hproper hglobalFailure normalSubgroup hminimal
  let projection := QuotientGroup.mk' normalSubgroup
  have hkernel : projection.ker = normalSubgroup := QuotientGroup.ker_mk' normalSubgroup
  let : Group.IsSolvable projection.ker := by rw [hkernel]; infer_instance
  have hquotientB := hsmaller normalSubgroup inferInstance
    (MinimalBCenter.quotient_card_lt normalSubgroup hminimal.prop.2)
  obtain ⟨localComponent, hlocal, hlocalNotQuasisimple, hnotContained, himageQuasisimple,
    hnotCentral⟩ := OddKernelBObstruction.exists_bad_component projection
      (QuotientGroup.mk'_surjective _) (by rwa [hkernel]) hquotientB twoSubgroup hne htwo hfailure
  let normalizer := Subgroup.normalizer (twoSubgroup : Set G)
  let component := localComponent.map normalizer.subtype
  have hcomponentLe : component ≤ normalizer := Subgroup.map_subtype_le _
  have hcomponent : TwoComponents.IsTwoComponent (component.subgroupOf normalizer) := by
    change TwoComponents.IsTwoComponent ((localComponent.map normalizer.subtype).comap
      normalizer.subtype)
    rw [Subgroup.comap_map_eq_self_of_injective normalizer.subtype_injective]
    exact hlocal
  let : Group.IsPerfect localComponent := ⟨TwoComponents.perfect hlocal⟩
  let : Group.IsPerfect component := Group.IsPerfect.map normalizer.subtype
  have hnotQuasisimple : ¬ IsQuasisimple component := by
    intro hquasisimple
    exact hlocalNotQuasisimple (Components.quasisimple_of_equiv
      (localComponent.equivMapOfInjective normalizer.subtype normalizer.subtype_injective)
      hquasisimple)
  have hcentralizes := TwoComponentCentralizers.le_ambient_centralizer component twoSubgroup
    normalizer hcomponentLe Subgroup.le_normalizer le_rfl hcomponent htwo
  rw [hkernel] at hnotCentral
  exact ⟨normalSubgroup, inferInstance, hle, hminimal, hcharacteristic, hsolvable, hodd, component,
    hcomponentLe, hcomponent, inferInstance, hnotQuasisimple, hnotContained,
    hcentralizes, himageQuasisimple, hnotCentral⟩


end CFSG.ComponentClassification.MinimalBOddWitness
