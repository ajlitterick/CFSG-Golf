module

public import CFSG.ClassicalInvolution.AschTight.S1916Dich
public import CFSG.ClassicalInvolution.AschTight.Sec19L98
public import CFSG.ClassicalInvolution.AschTight.S1916InA

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_comm_of_normalizes {H : Subgroup G} {x t : G}
    (hxH : ∀ q ∈ H, x * q = q * x) (htH : t ∈ Subgroup.normalizer (H : Set G)) :
    ∀ q ∈ H, (x * t * x⁻¹ * t⁻¹) * q = q * (x * t * x⁻¹ * t⁻¹) := by
  intro q hq
  have hq' : t⁻¹ * q * t ∈ H := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (H : Set G)).inv_mem htH) q).mp
      hq
    rwa [inv_inv] at this
  have h1 := hxH _ hq'
  have h2 : x⁻¹ * (t⁻¹ * q * t) = (t⁻¹ * q * t) * x⁻¹ := by
    calc x⁻¹ * (t⁻¹ * q * t) = x⁻¹ * ((t⁻¹ * q * t) * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * (t⁻¹ * q * t)) * x⁻¹ := by rw [h1]
      _ = (t⁻¹ * q * t) * x⁻¹ := by group
  calc x * t * x⁻¹ * t⁻¹ * q = x * t * (x⁻¹ * (t⁻¹ * q * t)) * t⁻¹ := by group
    _ = x * t * ((t⁻¹ * q * t) * x⁻¹) * t⁻¹ := by rw [h2]
    _ = (x * q) * t * x⁻¹ * t⁻¹ := by group
    _ = (q * x) * t * x⁻¹ * t⁻¹ := by rw [hxH q hq]
    _ = q * (x * t * x⁻¹ * t⁻¹) := by group

variable {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G}

theorem Ctx12.centralizer_le_normalizer_L (c : Ctx12 p f K z S W L t) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hd := c.hd
  have hzK := isUniqueInvolution_of_tight hd.tight.toTightBranch
  obtain ⟨g, hg⟩ := c.data.memL
  change conjSub g K = L at hg
  have e : t = g * z * g⁻¹ := c.data.invL.eq (hg ▸ hzK.conj g)
  rw [e, ← hg]
  exact centralizer_le_normalizer_conjSub (sd_normalizer_eq hd).ge g

theorem Ctx12.four_le_card_V [IsSimpleGroup G] (c : Ctx12 p f K z S W L t) :
    4 ≤ Nat.card ↥(L ⊓ W) := by
  have ht := c.hd.tight
  have h8 := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member
    (mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) (sd_isSylow2In_R c.hd))).2
  have := c.card_R
  omega

theorem Ctx12.two_lt_card_L_inf_S [IsSimpleGroup G] (c : Ctx12 p f K z S W L t) :
    2 < Nat.card ↥(L ⊓ (S : Subgroup G)) := by
  have h1 := c.four_le_card_V
  have h2 := Subgroup.card_le_of_le (inf_le_inf_left L c.hd.hWS)
  omega


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
