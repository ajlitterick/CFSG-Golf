module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem normal_pSubgroup_le_pCore {Ambient : Type groupUniverse} [Group Ambient]
    {prime : ℕ} (NormalSubgroup : Subgroup Ambient) (hnormal : NormalSubgroup.Normal)
    (hpgroup : IsPGroup prime NormalSubgroup) : NormalSubgroup ≤ pCore prime Ambient :=
  le_sSup ⟨hnormal, hpgroup⟩

theorem pCore_eq_maximal_normal_pSubgroup (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] (prime : ℕ) :
    ∃ Core : Subgroup Ambient,
      Core.Normal ∧ IsPGroup prime Core ∧ pCore prime Ambient = Core := by
  have hbot : (⊥ : Subgroup Ambient).Normal ∧ IsPGroup prime (⊥ : Subgroup Ambient) :=
    ⟨inferInstance, IsPGroup.of_bot⟩
  obtain ⟨Core, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun NormalSubgroup : Subgroup Ambient =>
      NormalSubgroup.Normal ∧ IsPGroup prime NormalSubgroup) hbot
  obtain ⟨hnormal, hpgroup⟩ := hmaximal.prop
  refine ⟨Core, hnormal, hpgroup, le_antisymm ?_ ?_⟩
  · rw [CFSG.pCore_eq_iSup]
    apply iSup_le
    intro NormalSubgroup
    apply iSup_le
    intro hsubgroupNormal
    apply iSup_le
    intro hsubgroupPGroup
    let : Core.Normal := hnormal
    let : NormalSubgroup.Normal := hsubgroupNormal
    have hsup : (Core ⊔ NormalSubgroup).Normal ∧
        IsPGroup prime (Core ⊔ NormalSubgroup : Subgroup Ambient) :=
      ⟨inferInstance, hpgroup.to_sup_of_normal_left hsubgroupPGroup⟩
    exact le_trans le_sup_right (hmaximal.2 hsup le_sup_left)
  · exact normal_pSubgroup_le_pCore Core hnormal hpgroup

theorem pCore_normal (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    (prime : ℕ) : (pCore prime Ambient).Normal := by
  obtain ⟨Core, hnormal, _, hcore⟩ := pCore_eq_maximal_normal_pSubgroup Ambient prime
  exact hcore ▸ hnormal

theorem pCore_isPGroup (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    (prime : ℕ) : IsPGroup prime (pCore prime Ambient) := by
  obtain ⟨Core, _, hpgroup, hcore⟩ := pCore_eq_maximal_normal_pSubgroup Ambient prime
  exact hcore ▸ hpgroup

theorem pCoreOf_le {Ambient : Type groupUniverse} [Group Ambient] (prime : ℕ)
    (Local : Subgroup Ambient) : pCoreOf prime Local ≤ Local := by
  intro element helement
  obtain ⟨preimage, _, hpreimage⟩ := helement
  exact hpreimage ▸ preimage.property

theorem pCoreOf_isPGroup {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    (prime : ℕ) (Local : Subgroup Ambient) : IsPGroup prime (pCoreOf prime Local) := by
  exact (pCore_isPGroup Local prime).map Local.subtype

theorem normal_pSubgroup_le_pCoreOf {Ambient : Type groupUniverse} [Group Ambient]
    {prime : ℕ} (NormalSubgroup Local : Subgroup Ambient) (hle : NormalSubgroup ≤ Local)
    (hnormal : (NormalSubgroup.subgroupOf Local).Normal)
    (hpgroup : IsPGroup prime NormalSubgroup) : NormalSubgroup ≤ pCoreOf prime Local := by
  have hpgroupOf : IsPGroup prime (NormalSubgroup.subgroupOf Local) :=
    hpgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hcore := normal_pSubgroup_le_pCore (NormalSubgroup.subgroupOf Local) hnormal hpgroupOf
  have hmap := Subgroup.map_mono (f := Local.subtype) hcore
  rwa [Subgroup.map_subgroupOf_eq_of_le hle] at hmap

theorem twoLocal_core_ne_bot {Ambient : Type groupUniverse} [Group Ambient]
    (Local : Subgroup Ambient) (hlocal : IsTwoLocal Local) : pCoreOf 2 Local ≠ ⊥ := by
  obtain ⟨TwoSubgroup, hnontrivial, hpgroup, hnormalizer⟩ := hlocal
  have hle : TwoSubgroup ≤ Local := hnormalizer ▸ Subgroup.le_normalizer
  have hnormal : (TwoSubgroup.subgroupOf Local).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (le_of_eq hnormalizer)
  have hcore := normal_pSubgroup_le_pCoreOf TwoSubgroup Local hle hnormal hpgroup
  intro hbot
  apply hnontrivial
  exact le_antisymm (hbot ▸ hcore) bot_le

theorem pCoreOf_subgroupOf_normal {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (prime : ℕ) (Local : Subgroup Ambient) :
    ((pCoreOf prime Local).subgroupOf Local).Normal := by
  have heq : (pCoreOf prime Local).subgroupOf Local = pCore prime Local :=
    Subgroup.comap_map_eq_self_of_injective Local.subtype_injective _
  rw [heq]
  exact pCore_normal Local prime


end CFSG.LargeEvenClassification.Helpers
