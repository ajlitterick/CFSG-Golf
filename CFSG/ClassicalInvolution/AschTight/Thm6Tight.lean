module

public import CFSG.ClassicalInvolution.AschTight.MuZ2Final
public import CFSG.ClassicalInvolution.AschTight.WreathedData
public import CFSG.ClassicalInvolution.AschTight.C19Bridge
public import CFSG.ClassicalInvolution.AschTight.CStarCount

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]


variable {p f}

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem exists_sylow_setup (ht : S19R.TightStd p f K z) :
    ∃ (Q₀ : Sylow 2 K) (S : Sylow 2 G), (Q₀ : Subgroup K).map K.subtype ≤ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (((Q₀ : Subgroup K).map K.subtype : Subgroup G) :
        Set G) ∧
      (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) ∧
      (S : Subgroup G) ⊓ K ≤ (Q₀ : Subgroup K).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htb := ht.toTightBranch
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 K) := inferInstance
  set R : Subgroup G := (Q₀ : Subgroup K).map K.subtype with hRdef
  have hR : R ∈ RSet (CoreAssembly.conjClass K) :=
    ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩
  have hzR : IsUniqueInvolution R z :=
    isUniqueInvolution_of_mem_rSet_of_le htb hR (Subgroup.map_subtype_le _)
  obtain ⟨S, hRS⟩ := (Q₀.isPGroup'.map K.subtype).exists_le_sylow
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) := by
    intro s hs
    have hle : conjSubgroup s R ≤ (S : Subgroup G) := by
      intro x hx
      have hx' := mem_conjSubgroup_iff.mp hx
      have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hRS hx')) (Subgroup.inv_mem _ hs)
    exact conjSubgroup_eq_self_iff.mp
      (conjSubgroup_sylow_eq_of_tightD ht Q₀ S.isPGroup' hRS hle)
  refine ⟨Q₀, S, hRS, hSN, fun s hs => ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hzR.conj_eq (conjSub_eq_of_mem_normalizer (hSN hs))
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [h1]
  · have h2 : IsPGroup 2 (((S : Subgroup G) ⊓ K).subgroupOf K) :=
      (S.isPGroup'.to_le inf_le_left).comap_subtype
    have hle : (Q₀ : Subgroup K) ≤ ((S : Subgroup G) ⊓ K).subgroupOf K := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr ⟨hRS ⟨x, hx, rfl⟩, x.2⟩
    have heq := Q₀.3 h2 hle
    intro x hx
    have hxK : x ∈ K := hx.2
    have : (⟨x, hxK⟩ : K) ∈ ((S : Subgroup G) ⊓ K).subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at this
    exact ⟨⟨x, hxK⟩, this, rfl⟩


end CFSG.ClassicalInvolution.Disconnected.AschTight
