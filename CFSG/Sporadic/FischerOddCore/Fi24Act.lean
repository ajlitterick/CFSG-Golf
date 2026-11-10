
module

public import CFSG.Sporadic.Fi24.OctadAction
public import CFSG.Sporadic.FischerOddCore.CentralExt
public import CFSG.Sporadic.FischerOddCore.Fi24WitCheckInputs

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24 (R J M MR tR D24 jR cls)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

attribute [local instance] CFSG.Sporadic.Fi24.rAction


@[expose] def fi23ToR :
    CFSG.Sporadic.Fi23.J →* R :=
  jR.comp (M.subtype.comp
    (@MulEquiv.toMonoidHom CFSG.Sporadic.Fi23.J M inferInstance inferInstance
      Fi24.fi23EquivM.symm))

theorem fi23ToR_apply
    (u : CFSG.Sporadic.Fi23.J) :
    fi23ToR u = jR (Fi24.fi23EquivM.symm u : J) := rfl

theorem fi23ToR_mem
    (u : CFSG.Sporadic.Fi23.J) : fi23ToR u ∈ MR :=
  ⟨_, (Fi24.fi23EquivM.symm u).2, rfl⟩

theorem fi23ToR_injective :
    Function.Injective fi23ToR := by
  intro u v h
  rw [fi23ToR_apply, fi23ToR_apply] at h
  exact Fi24.fi23EquivM.symm.injective (Subtype.ext (Fi24.jR_injective h))

theorem exists_fi23ToR
    {m : R} (hm : m ∈ MR) : ∃ u, fi23ToR u = m := by
  obtain ⟨g, hg, rfl⟩ := hm
  exact ⟨Fi24.fi23EquivM ⟨g, hg⟩, by rw [fi23ToR_apply, MulEquiv.symm_apply_apply]⟩

theorem fi23ToR_a :
    fi23ToR CFSG.Sporadic.Fi23.a = jR (Fi24.mGen0 : J) := by
  rw [fi23ToR_apply, ← Fi24.fi23EquivM_mGen0, MulEquiv.symm_apply_apply]

theorem fi23ToR_b :
    fi23ToR CFSG.Sporadic.Fi23.b = jR (Fi24.mGen1 : J) := by
  rw [fi23ToR_apply, ← Fi24.fi23EquivM_mGen1, MulEquiv.symm_apply_apply]


theorem oddCore_eq_bot_of_normal_le {G : Type*} [Group G] [Finite G] {K L : Subgroup G}
    (hKL : K ≤ L) (hK : (K.subgroupOf L).Normal) (hL : CFSG.oddCore ↥L = ⊥) :
    CFSG.oddCore ↥K = ⊥ := by
  set N := (CFSG.oddCore ↥K).map K.subtype
  have hNK : N ≤ K := Subgroup.map_subtype_le _
  have hnormal : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk, hkn⟩ := hn
    have hconj : ∀ x ∈ K, (l : G) * x * (l : G)⁻¹ ∈ K := fun x hx => by
      have := hK.conj_mem ⟨x, hKL hx⟩ (Subgroup.mem_subgroupOf.2 hx) l
      rwa [Subgroup.mem_subgroupOf] at this
    have hconj' : ∀ x ∈ K, (l : G)⁻¹ * x * (l : G) ∈ K := fun x hx => by
      have := hK.conj_mem ⟨x, hKL hx⟩ (Subgroup.mem_subgroupOf.2 hx) l⁻¹
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    let φ : K ≃* K :=
      { toFun := fun x => ⟨l * x * (l : G)⁻¹, hconj x x.2⟩
        invFun := fun x => ⟨(l : G)⁻¹ * x * l, hconj' x x.2⟩
        left_inv := fun x => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
    refine ⟨φ k, map_oddCore_le φ ⟨k, hk, rfl⟩, ?_⟩
    change (l : G) * (k : G) * (l : G)⁻¹ = ((l * n * l⁻¹ : L) : G)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hkn]
    rfl
  have hodd : Odd (Nat.card (N.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNK.trans hKL)).toEquiv,
      Nat.card_congr ((CFSG.oddCore ↥K).equivMapOfInjective _ K.subtype_injective).toEquiv.symm]
    exact odd_card_oddCore
  have hle := le_oddCore_of_normal hnormal hodd
  rw [hL, le_bot_iff, Subgroup.subgroupOf_eq_bot] at hle
  have hbot : N = ⊥ := disjoint_self.1 (hle.mono_right (hNK.trans hKL))
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 hbot

end CFSG.Sporadic.FischerOddCore
