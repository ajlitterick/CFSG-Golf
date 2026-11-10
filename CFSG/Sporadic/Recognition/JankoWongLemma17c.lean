module

public import CFSG.Sporadic.Recognition.JankoWongLemma16c

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} {c : Ctx S}

theorem IsW.normalizer_le_normalizer_zpowers_a
    {W : Subgroup G} (hW : c.IsW W) :
    normalizer (W : Set G) ≤ normalizer ((zpowers (c.a : G) : Subgroup G) : Set G) := by
  have hc : ∀ g' ∈ normalizer (W : Set G), ∀ y ∈ centerW W, g' * y * g'⁻¹ ∈ centerW W := by
    intro g' hg' y hy
    obtain ⟨hyW, hyc⟩ := mem_centerW.mp hy
    refine mem_centerW.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg' y).mp hyW, fun w hw => ?_⟩
    have hw' : g'⁻¹ * w * g' ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer (W : Set G)).inv_mem hg') w).mp hw
      simpa using this
    have h1 := hyc _ hw'
    calc w * (g' * y * g'⁻¹) = g' * ((g'⁻¹ * w * g') * y) * g'⁻¹ := by group
      _ = g' * (y * (g'⁻¹ * w * g')) * g'⁻¹ := by rw [h1]
      _ = g' * y * g'⁻¹ * w := by group
  intro g hg
  rw [← hW.centerW_eq_zpowers_a]
  refine Subgroup.mem_normalizer_iff.mpr (fun y => ⟨fun hy => hc g hg y hy, fun hy => ?_⟩)
  have h := hc g⁻¹ ((normalizer (W : Set G)).inv_mem hg) _ hy
  have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  rwa [e] at h

theorem IsW.normalizer_a_inf_NG_le
    {W : Subgroup G} (hW : c.IsW W) :
    c.NG ⊓ normalizer ((zpowers (c.a : G) : Subgroup G) : Set G) ≤ normalizer (W : Set G) := by
  obtain ⟨-, -, hmax⟩ := hW.Ca_facts
  have hconj : ∀ g' ∈ c.NG ⊓ normalizer ((zpowers (c.a : G) : Subgroup G) : Set G),
      ∀ w ∈ W, g' * w * g'⁻¹ ∈ W := by
    intro g' hg' w hw
    set W' : Subgroup G := W.map (MulAut.conj g').toMonoidHom with hW'
    have hW'K : W' ≤ c.NG ⊓ centralizer ({(c.a : G)} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      have hyc : (MulAut.conj g').toMonoidHom y = g' * y * g'⁻¹ := by simp
      rw [hyc]
      refine ⟨c.NG.mul_mem (c.NG.mul_mem hg'.1 (hW.le_NG hy)) (c.NG.inv_mem hg'.1),
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hg'i : g'⁻¹ ∈ normalizer ((zpowers (c.a : G) : Subgroup G) : Set G) :=
        (normalizer ((zpowers (c.a : G) : Subgroup G) : Set G)).inv_mem hg'.2
      have hmem : g'⁻¹ * (c.a : G) * g'⁻¹⁻¹ ∈ zpowers (c.a : G) :=
        (Subgroup.mem_normalizer_iff.mp hg'i (c.a : G)).mp (Subgroup.mem_zpowers _)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hyk : y * (c.a : G) ^ k = (c.a : G) ^ k * y :=
        (Commute.zpow_right (show Commute y (c.a : G) from hW.comm_a y hy) k).eq
      have hak : (c.a : G) = g' * (c.a : G) ^ k * g'⁻¹ := by
        rw [hk]; group
      calc g' * y * g'⁻¹ * (c.a : G) = g' * y * g'⁻¹ * (g' * (c.a : G) ^ k * g'⁻¹) := by
            rw [← hak]
        _ = g' * (y * (c.a : G) ^ k) * g'⁻¹ := by group
        _ = g' * ((c.a : G) ^ k * y) * g'⁻¹ := by rw [hyk]
        _ = (g' * (c.a : G) ^ k * g'⁻¹) * (g' * y * g'⁻¹) := by group
        _ = (c.a : G) * (g' * y * g'⁻¹) := by rw [← hak]
    have hW'p : IsPGroup 3 W' := hW.isPGroup.map _
    have := hmax W' hW'K hW'p
    exact this ⟨w, hw, by simp⟩
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr (fun w => ⟨fun hw => hconj g hg w hw, fun hw => ?_⟩)
  have hgi : g⁻¹ ∈ c.NG ⊓ normalizer ((zpowers (c.a : G) : Subgroup G) : Set G) :=
    (c.NG ⊓ normalizer ((zpowers (c.a : G) : Subgroup G) : Set G)).inv_mem hg
  have h := hconj g⁻¹ hgi _ hw
  have e : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
  rwa [e] at h

theorem IsW.normalizer_eq
    {W : Subgroup G} (hW : c.IsW W) :
    normalizer (W : Set G) =
      c.NG ⊓ normalizer ((zpowers (c.a : G) : Subgroup G) : Set G) :=
  le_antisymm (le_inf hW.normalizer_le_NG hW.normalizer_le_normalizer_zpowers_a)
    hW.normalizer_a_inf_NG_le

theorem IsW.card_normalizer
    {W : Subgroup G} (hW : c.IsW W) : Nat.card ↥(normalizer (W : Set G)) = 5832 := by
  obtain ⟨e, he, hea⟩ := c.exists_mem_Bg_inv_a
  have hU : c.NG ⊓ normalizer ((zpowers (c.a : G) : Subgroup G) : Set G) ≤
      normalizer ((zpowers (c.a : G) : Subgroup G) : Set G) := inf_le_right
  have h2 := card_eq_two_mul_inf_centralizer (x := (c.a : G)) (e := e) orderOf_aG hU
    ⟨c.Bg_le_NG he, mem_normalizer_zpowers_of_inv hea⟩ hea
  have hinf : (c.NG ⊓ normalizer ((zpowers (c.a : G) : Subgroup G) : Set G)) ⊓
      centralizer ({(c.a : G)} : Set G) = c.NG ⊓ centralizer ({(c.a : G)} : Set G) := by
    exact le_antisymm (inf_le_inf inf_le_left le_rfl)
      (le_inf (le_inf inf_le_left
        (inf_le_right.trans (centralizer_le_normalizer_zpowers (c.a : G)))) inf_le_right)
  rw [hW.normalizer_eq, h2, hinf, c.card_NG_inf_centralizer_a]


end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong
