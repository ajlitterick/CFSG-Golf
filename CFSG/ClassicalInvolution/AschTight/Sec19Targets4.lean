module

public import CFSG.ClassicalInvolution.AschTight.E2StarTargets
public import CFSG.ClassicalInvolution.AschTight.C195
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C19_11bTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT p f K z S W L t V →
      (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
          Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L = ⊥

@[expose] def C19_11aTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      (S : Subgroup G) ⊓ sec19Y K z ⊓ Subgroup.centralizer (W : Set G) ≤ W


variable {p f}


variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_inf_of_mem_cStar {K : Subgroup G} {S : Subgroup G} (hS : IsPGroup 2 S)
    {x : G} (hx : x ∈ cStar K) (hxS : x ∈ S) :
    x ∈ Subgroup.centralizer ((S ⊓ K : Subgroup G) : Set G) := by
  obtain ⟨hxN, h⟩ := mem_cStar_iff.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h1 := h ⟨r, hr.2⟩
  set y : K := (normalizerConj K ⟨x, hxN⟩ ⟨r, hr.2⟩)⁻¹ * ⟨r, hr.2⟩ with hy
  have hyS : (y : G) ∈ S := by
    rw [hy, Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply_coe]
    exact S.mul_mem (S.inv_mem (S.mul_mem (S.mul_mem hxS hr.1) (S.inv_mem hxS))) hr.1
  have h2 : IsPGroup 2 ↥((S ⊓ K).subgroupOf K) := (hS.to_le inf_le_left).comap_subtype
  have h3 : y ∈ (S ⊓ K).subgroupOf K ⊓ classicalInvolutionOddCore ↥K :=
    ⟨Subgroup.mem_subgroupOf.mpr ⟨hyS, y.2⟩, h1⟩
  rw [inf_oddCore_eq_bot h2, Subgroup.mem_bot, hy, inv_mul_eq_one] at h3
  have h4 : x * r * x⁻¹ = r := by
    simpa [normalizerConj_apply_coe] using congrArg Subtype.val h3
  calc r * x = (x * r * x⁻¹) * x := by rw [h4]
    _ = x * r := by group


end CFSG.ClassicalInvolution.Disconnected.AschTight
