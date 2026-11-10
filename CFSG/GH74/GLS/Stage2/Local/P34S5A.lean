module

public import CFSG.GH74.GLS.Stage2.Local.P34Step0
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Local.P34Stmt
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open scoped Pointwise
open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

section Sylow

variable {G : Type} [Group G]

theorem mem_smul_sylow_iff (Q : Sylow 2 G) (g x : G) :
    x ∈ ((g • Q : Sylow 2 G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (Q : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem]
  have : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
    rw [MulAut.smul_def]
    simp
  rw [this]

variable [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem exists_sylow_S (hctx : Stage2Ctx G z k S) : ∃ P : Sylow 2 G, (P : Subgroup G) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hctx.sylow_top
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨-, hP, hdvd⟩ := hS
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hP.toSylow hdvd, rfl⟩

theorem exists_conj_mem_S (hctx : Stage2Ctx G z k S) {u : G} (hu : IsPGroup 2 ↥(zpowers u)) :
    ∃ g : G, g * u * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_S hctx
  obtain ⟨Q, hQ⟩ := hu.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  have hmem : g * u * g⁻¹ ∈ ((g • Q : Sylow 2 G) : Subgroup G) := by
    rw [mem_smul_sylow_iff]
    have := hQ (mem_zpowers u)
    simpa [mul_assoc] using this
  rw [hg, hP] at hmem
  exact hmem

theorem isConj_of_isCentralInvolution (hctx : Stage2Ctx G z k S) {x : G} (hx : IsCentralInvolution x) :
    IsConj z x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hx2, S', hxS', hxc⟩ := hx
  obtain ⟨P, hP⟩ := exists_sylow_S hctx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' P
  have hmem : g * x * g⁻¹ ∈ ((g • S' : Sylow 2 G) : Subgroup G) := by
    rw [mem_smul_sylow_iff]
    simpa [mul_assoc] using hxS'
  rw [hg, hP] at hmem
  have hcomm : ∀ s ∈ S, s * (g * x * g⁻¹) = (g * x * g⁻¹) * s := by
    intro s hs
    have hs' : g⁻¹ * s * g ∈ (S' : Subgroup G) := by
      have : s ∈ ((g • S' : Sylow 2 G) : Subgroup G) := by rw [hg, hP]; exact hs
      exact (mem_smul_sylow_iff S' g s).1 this
    have := hxc _ hs'
    calc s * (g * x * g⁻¹) = g * ((g⁻¹ * s * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by rw [this]
      _ = (g * x * g⁻¹) * s := by group
  have hord : orderOf (g * x * g⁻¹) = 2 := by
    rw [← hx2]
    exact (orderOf_eq_of_isConj' (isConj_iff.2 ⟨g, rfl⟩)).symm
  have hz := hctx.data.base.zcen _ hmem hcomm hord
  rw [isConj_iff]
  refine ⟨g⁻¹, ?_⟩
  rw [← hz]
  group

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf_eq_two {u : G} (hu : orderOf u = 2) : IsPGroup 2 ↥(zpowers u) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])

theorem exists_nonCentral_in_S (hctx : Stage2Ctx G z k S) {x' : G} (hx2 : orderOf x' = 2)
    (hx : ¬ IsConj z x') : ∃ x ∈ S, IsNonCentralInvolution x := by
  obtain ⟨g, hg⟩ := exists_conj_mem_S hctx (isPGroup_zpowers_of_orderOf_eq_two hx2)
  have hconj : IsConj x' (g * x' * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  refine ⟨g * x' * g⁻¹, hg, ?_, fun hc => hx ?_⟩
  · rw [← hx2]
    exact (orderOf_eq_of_isConj' hconj).symm
  · exact (isConj_of_isCentralInvolution hctx hc).trans hconj.symm

end Sylow

section Fus

variable {G : Type} [Group G] [Finite G] {z : G}

theorem centralizer_le_of_fus {H : Subgroup G} (hFUS : FUS H) (hCH : Cen z ≤ H) (hz2 : orderOf z = 2) {u : G}
    (huH : u ∈ H) (hu2 : orderOf u = 2) (hc : IsConj z u) : centralizer ({u} : Set G) ≤ H := by
  have hzH : z ∈ H := z_mem_of_cen_le hCH
  have hord : ∀ {w : G} (hw : w ∈ H), orderOf w = 2 → orderOf (⟨w, hw⟩ : ↥H) = 2 := by
    intro w hw h
    rw [← h]
    exact (Subgroup.orderOf_coe (⟨w, hw⟩ : ↥H)).symm
  have h1 : IsConj (⟨z, hzH⟩ : ↥H) ⟨u, huH⟩ :=
    isConj_of_mk_isConj H (hord hzH hz2) (hord huH hu2)
      (hFUS ⟨z, hzH⟩ ⟨u, huH⟩ (hord hzH hz2) (hord huH hu2) hc)
  obtain ⟨c, hc'⟩ := isConj_iff.1 h1
  have hcz : (c : G) * z * (c : G)⁻¹ = u := congrArg Subtype.val hc'
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hcg : (c : G)⁻¹ * g * (c : G) ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzu : z = (c : G)⁻¹ * u * (c : G) := by rw [← hcz]; group
    calc (c : G)⁻¹ * g * (c : G) * z = (c : G)⁻¹ * (g * u) * (c : G) := by rw [hzu]; group
      _ = (c : G)⁻¹ * (u * g) * (c : G) := by rw [hg]
      _ = z * ((c : G)⁻¹ * g * (c : G)) := by rw [hzu]; group
  have hcgH : (c : G)⁻¹ * g * (c : G) ∈ H := hCH hcg
  have hg' : g = (c : G) * ((c : G)⁻¹ * g * (c : G)) * (c : G)⁻¹ := by group
  rw [hg']
  exact H.mul_mem (H.mul_mem c.2 hcgH) (H.inv_mem c.2)

end Fus

section Choice


end Choice

end CFSG.GH74.GLS.Stage2.Local.P34
