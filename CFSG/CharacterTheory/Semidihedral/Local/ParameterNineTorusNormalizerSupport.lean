module

public import CFSG.CharacterTheory.Semidihedral.Local.OddCoreQuotientSimpleSupport
public import CFSG.LinearAlgebra.SL2OrderFifteen
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
public import CFSG.CharacterTheory.Semidihedral.ActualFourGroupNormalizer

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Local

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage


theorem exists_sylow_eq_of_order_four_square_of_not_dvd {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {t : G} (hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t})
    (hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t)
    (H P₀ : Subgroup G) (hP₀H : P₀ ≤ H) (hP₀ : Nat.card P₀ = 8) {d : G} (hdP : d ∈ P₀)
    (hd4 : orderOf d = 4) (hd2 : d ^ 2 = t)
    (hCH : ¬ 2 ^ 4 ∣ Nat.card (Subgroup.centralizer {t} ⊓ H : Subgroup G)) :
    ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = P₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP₀' : Nat.card (P₀.subgroupOf H) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀H).toEquiv, hP₀]
  have hP₀p : IsPGroup 2 (P₀.subgroupOf H) := IsPGroup.of_card (n := 3) (by rw [hP₀']; norm_num)
  obtain ⟨T, hT⟩ := hP₀p.exists_le_sylow
  have hTp : IsPGroup 2 ((T : Subgroup H).map H.subtype) := T.isPGroup'.map _
  obtain ⟨S', hS'⟩ := hTp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
  have hmemS : ∀ x ∈ (T : Subgroup H).map H.subtype, g⁻¹ * x * g ∈ (S : Subgroup G) := by
    intro x hx
    have h : x ∈ ((g • S : Sylow 2 G) : Subgroup G) := hg ▸ hS' hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
    simpa [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply] using h
  have hdT : d ∈ (T : Subgroup H).map H.subtype :=
    ⟨⟨d, hP₀H hdP⟩, hT (show (⟨d, hP₀H hdP⟩ : H) ∈ P₀.subgroupOf H from hdP), rfl⟩
  have hgC : g ∈ Subgroup.centralizer {t} := by
    have hy := hmemS d hdT
    have hy4 : orderOf (g⁻¹ * d * g) = 4 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) d
      rw [MulAut.conj_apply, inv_inv] at h
      rw [h, hd4]
    have hy2 := hS4 _ hy hy4
    have hconj : g⁻¹ * t * g = t := by
      calc g⁻¹ * t * g = g⁻¹ * d ^ 2 * g := by rw [hd2]
        _ = (g⁻¹ * d * g) ^ 2 := by rw [sq, sq]; group
        _ = t := hy2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * t = g * (g⁻¹ * t * g) := by rw [hconj]
      _ = t * g := by group
  have hTC : (T : Subgroup H).map H.subtype ≤ Subgroup.centralizer {t} ⊓ H := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hxS := hSC (hmemS x hx)
      rw [Subgroup.mem_centralizer_singleton_iff] at hxS hgC ⊢
      have hg' : g⁻¹ * t = t * g⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgC, mul_assoc, mul_inv_cancel, mul_one]
      calc x * t = g * (g⁻¹ * x * g) * (g⁻¹ * t) := by group
        _ = g * (g⁻¹ * x * g) * (t * g⁻¹) := by rw [hg']
        _ = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by group
        _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [hxS]
        _ = (g * t) * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = (t * g) * (g⁻¹ * x * g) * g⁻¹ := by rw [hgC]
        _ = t * x := by group
    · obtain ⟨y, -, rfl⟩ := hx
      exact y.2
  have hTcard : Nat.card ((T : Subgroup H).map H.subtype) = Nat.card T :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hT8 : Nat.card T ∣ 8 := by
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    have hdvd : 2 ^ k ∣ Nat.card (Subgroup.centralizer {t} ⊓ H : Subgroup G) :=
      hk ▸ hTcard ▸ Subgroup.card_dvd_of_le hTC
    have hk3 : k ≤ 3 := by
      by_contra hk
      exact hCH ((pow_dvd_pow 2 (by omega : 4 ≤ k)).trans hdvd)
    rw [hk]
    exact (pow_dvd_pow 2 hk3).trans (by norm_num)
  have hTeq : P₀.subgroupOf H = T := by
    apply Subgroup.eq_of_le_of_card_ge hT
    rw [hP₀']
    exact Nat.le_of_dvd (by norm_num) hT8
  refine ⟨T, ?_⟩
  rw [← hTeq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP₀H]


end CFSG.Semidihedral.Local
