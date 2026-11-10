module

public import CFSG.RankThree.GF2n.Parrott.Section2Q8Final
public import CFSG.RankThree.GF2n.Parrott.OrthogonalV
public import CFSG.RankThree.GF2n.Parrott.Section2J0Normal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

section PolarForm

variable (h : Tim79a.ParrottHyp z)

theorem polarVZMod_pi_mul_left (x₁ x₂ y : J z) :
    polarVZMod h (QuotientV.pi z (x₁ * x₂)) (QuotientV.pi z y) =
      polarVZMod h (QuotientV.pi z x₁) (QuotientV.pi z y) +
        polarVZMod h (QuotientV.pi z x₂) (QuotientV.pi z y) := by
  have hcomm : Commute (x₁ : G) ⁅(x₂ : G), (y : G)⁆ := by
    have hmem : ⁅(x₂ : G), (y : G)⁆ ∈ Subgroup.zpowers z :=
      commutator_mem_zpowers_z h x₂.2 y.2
    have hcent : ⁅(x₂ : G), (y : G)⁆ ∈ Subgroup.centralizer (H z : Set G) :=
      zpowers_centralizes_H h hmem
    exact Subgroup.mem_centralizer_iff.mp hcent (x₁ : G) (J_le_H x₁.2)
  have hcommut : ⁅((x₁ * x₂ : J z) : G), (y : G)⁆ =
      ⁅(x₂ : G), (y : G)⁆ * ⁅(x₁ : G), (y : G)⁆ := by
    simpa using CFSG.GroupTheory.SuzukiTwoGroup.commutatorElement_mul_left_of_commute
      (x := (x₁ : G)) (x' := (x₂ : G)) (y := (y : G)) hcomm
  have h1 : polarV h (QuotientV.pi z (x₁ * x₂)) (QuotientV.pi z y) =
      polarV h (QuotientV.pi z x₂) (QuotientV.pi z y) *
        polarV h (QuotientV.pi z x₁) (QuotientV.pi z y) := by
    rw [polarV_pi, polarV_pi, polarV_pi]
    apply Subtype.ext
    simpa using hcommut
  rw [polarVZMod, polarVZMod, polarVZMod, h1, map_mul, toAdd_mul]
  exact add_comm _ _

theorem polarVZMod_pi_mul_right (x y₁ y₂ : J z) :
    polarVZMod h (QuotientV.pi z x) (QuotientV.pi z (y₁ * y₂)) =
      polarVZMod h (QuotientV.pi z x) (QuotientV.pi z y₁) +
        polarVZMod h (QuotientV.pi z x) (QuotientV.pi z y₂) := by
  have hcomm : Commute ((x : G) * (y₁ : G) * (x : G)⁻¹) ⁅(x : G), (y₂ : G)⁆ := by
    have hmem : ⁅(x : G), (y₂ : G)⁆ ∈ Subgroup.zpowers z :=
      commutator_mem_zpowers_z h x.2 y₂.2
    have hcent : ⁅(x : G), (y₂ : G)⁆ ∈ Subgroup.centralizer (H z : Set G) :=
      zpowers_centralizes_H h hmem
    have hxH : (x : G) * (y₁ : G) * (x : G)⁻¹ ∈ H z :=
      (H z).mul_mem ((H z).mul_mem (J_le_H x.2) (J_le_H y₁.2)) ((H z).inv_mem (J_le_H x.2))
    exact Subgroup.mem_centralizer_iff.mp hcent ((x : G) * (y₁ : G) * (x : G)⁻¹) hxH
  have hcommut : ⁅(x : G), ((y₁ * y₂ : J z) : G)⁆ =
      ⁅(x : G), (y₂ : G)⁆ * ⁅(x : G), (y₁ : G)⁆ := by
    simpa using CFSG.GroupTheory.SuzukiTwoGroup.commutatorElement_mul_right_of_commute
      (x := (x : G)) (y := (y₁ : G)) (y' := (y₂ : G)) hcomm
  have h1 : polarV h (QuotientV.pi z x) (QuotientV.pi z (y₁ * y₂)) =
      polarV h (QuotientV.pi z x) (QuotientV.pi z y₂) *
        polarV h (QuotientV.pi z x) (QuotientV.pi z y₁) := by
    rw [polarV_pi, polarV_pi, polarV_pi]
    apply Subtype.ext
    simpa using hcommut
  rw [polarVZMod, polarVZMod, polarVZMod, h1, map_mul, toAdd_mul]
  exact add_comm _ _

theorem polarVZMod_add (v w u : QuotientV.V z) :
    polarVZMod h (v * w) u = polarVZMod h v u + polarVZMod h w u := by
  obtain ⟨x, rfl⟩ := QuotientV.pi_surjective z v
  obtain ⟨y, rfl⟩ := QuotientV.pi_surjective z w
  obtain ⟨p, rfl⟩ := QuotientV.pi_surjective z u
  rw [← map_mul]
  exact polarVZMod_pi_mul_left h x y p

theorem polarVZMod_add_right (v w u : QuotientV.V z) :
    polarVZMod h v (w * u) = polarVZMod h v w + polarVZMod h v u := by
  obtain ⟨x, rfl⟩ := QuotientV.pi_surjective z v
  obtain ⟨y, rfl⟩ := QuotientV.pi_surjective z w
  obtain ⟨p, rfl⟩ := QuotientV.pi_surjective z u
  rw [← map_mul]
  exact polarVZMod_pi_mul_right h x y p


theorem polarVZMod_one_left (w : QuotientV.V z) : polarVZMod h 1 w = 0 := by
  obtain ⟨y, rfl⟩ := QuotientV.pi_surjective z w
  rw [show (1 : QuotientV.V z) = QuotientV.pi z 1 by simp, polarVZMod, polarV_pi]
  simp

theorem polarVZMod_one_right (v : QuotientV.V z) : polarVZMod h v 1 = 0 := by
  obtain ⟨x, rfl⟩ := QuotientV.pi_surjective z v
  rw [show (1 : QuotientV.V z) = QuotientV.pi z 1 by simp, polarVZMod, polarV_pi]
  simp

noncomputable def commutatorBilinForm :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    LinearMap.BilinForm (ZMod 2) (Additive (QuotientV.V z)) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  refine LinearMap.mk₂ (ZMod 2)
    (fun v w => polarVZMod h (Additive.toMul v) (Additive.toMul w)) ?_ ?_ ?_ ?_
  · intro v₁ v₂ w
    simp only [toMul_add]
    exact polarVZMod_add h (Additive.toMul v₁) (Additive.toMul v₂) (Additive.toMul w)
  · intro c v w
    have hc : c = 0 ∨ c = 1 := by
      have hlt : c.val < 2 := ZMod.val_lt c
      have hval : c.val = 0 ∨ c.val = 1 := by omega
      rcases hval with h | h
      · left
        exact ZMod.val_injective 2 (by simpa using h)
      · right
        exact ZMod.val_injective 2 (by rw [ZMod.val_one]; exact h)
    rcases hc with rfl | rfl
    · have h0 : (0 : ZMod 2) • v = 0 := zero_smul _ _
      rw [h0]
      change polarVZMod h 1 (Additive.toMul w) =
        (0 : ZMod 2) • polarVZMod h (Additive.toMul v) (Additive.toMul w)
      rw [polarVZMod_one_left, zero_smul]
    · rw [one_smul, one_smul]
  · intro v w₁ w₂
    simp only [toMul_add]
    exact polarVZMod_add_right h (Additive.toMul v) (Additive.toMul w₁) (Additive.toMul w₂)
  · intro c v w
    have hc : c = 0 ∨ c = 1 := by
      have hlt : c.val < 2 := ZMod.val_lt c
      have hval : c.val = 0 ∨ c.val = 1 := by omega
      rcases hval with h | h
      · left
        exact ZMod.val_injective 2 (by simpa using h)
      · right
        exact ZMod.val_injective 2 (by rw [ZMod.val_one]; exact h)
    rcases hc with rfl | rfl
    · have h0 : (0 : ZMod 2) • w = 0 := zero_smul _ _
      rw [h0]
      change polarVZMod h (Additive.toMul v) 1 =
        (0 : ZMod 2) • polarVZMod h (Additive.toMul v) (Additive.toMul w)
      rw [polarVZMod_one_right, zero_smul]
    · rw [one_smul, one_smul]

@[simp] theorem commutatorBilinForm_apply (v w : QuotientV.V z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    commutatorBilinForm h (Additive.ofMul v) (Additive.ofMul w) = polarVZMod h v w := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rfl

theorem commutatorBilinForm_isRefl :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    (commutatorBilinForm h).IsRefl := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  intro x y hxy
  change polarVZMod h (Additive.toMul y) (Additive.toMul x) = 0
  rw [polarVZMod_comm]
  exact hxy

theorem commutatorBilinForm_nondegenerate :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    (commutatorBilinForm h).Nondegenerate := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  constructor
  · intro x hx
    have hx' : ∀ w : QuotientV.V z, polarVZMod h (Additive.toMul x) w = 0 := by
      intro w
      have hw := hx (Additive.ofMul w)
      change polarVZMod h (Additive.toMul x) w = 0 at hw
      exact hw
    have hzero := polarVZMod_nondegenerate h (Additive.toMul x) hx'
    simpa using congrArg Additive.ofMul hzero
  · intro y hy
    have hy' : ∀ w : QuotientV.V z, polarVZMod h w (Additive.toMul y) = 0 := by
      intro w
      have hw := hy (Additive.ofMul w)
      change polarVZMod h w (Additive.toMul y) = 0 at hw
      exact hw
    have hfix : ∀ w : QuotientV.V z, polarVZMod h (Additive.toMul y) w = 0 := by
      intro w
      rw [polarVZMod_comm]
      exact hy' w
    have hzero := polarVZMod_nondegenerate h (Additive.toMul y) hfix
    simpa using congrArg Additive.ofMul hzero

end PolarForm

section Determination

variable (h : Tim79a.ParrottHyp z)


@[expose] noncomputable def commutatorVSubmodule (σ : ↥(H z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  AddSubgroup.toZModSubmodule (n := 2) (commutatorV h σ).toAddSubgroup

@[expose] noncomputable def VComplementLinearMap (σ : ↥(H z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Additive (QuotientV.V z) →ₗ[ZMod 2] Additive (QuotientV.V z) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  exact (MonoidHom.toAdditive (VComplementHom h σ)).toZModLinearMap 2

@[simp] theorem VComplementLinearMap_apply (σ : ↥(H z)) (v : QuotientV.V z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    VComplementLinearMap h σ (Additive.ofMul v) = Additive.ofMul (VComplementHom h σ v) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rfl

theorem range_VComplementLinearMap {σ : ↥(H z)} (hσ : orderOf σ = 3) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    LinearMap.range (VComplementLinearMap h σ) = commutatorVSubmodule h σ := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  ext x
  rw [LinearMap.mem_range]
  change (∃ y, VComplementLinearMap h σ y = x) ↔
    x ∈ (commutatorV h σ).toAddSubgroup
  rw [Additive.mem_toAddSubgroup, commutatorV_eq_range (z := z) h hσ]
  constructor
  · rintro ⟨y, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨Additive.toMul y, rfl⟩
  · rintro ⟨v, hv⟩
    refine ⟨Additive.ofMul v, ?_⟩
    rw [VComplementLinearMap_apply, hv]
    simp

theorem ker_VComplementLinearMap {σ : ↥(H z)} (hσ : orderOf σ = 3) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    LinearMap.ker (VComplementLinearMap h σ) = fixSubmodule h σ := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rw [fixSubmodule_eq_ker_VComplementHom (z := z) h hσ]
  ext x
  rw [LinearMap.mem_ker, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup,
    MonoidHom.mem_ker]
  change VComplementHom h σ (Additive.toMul x) = 1 ↔
    Additive.toMul x ∈ (VComplementHom h σ).ker
  rfl

end Determination

section Orthogonal

variable (h : Tim79a.ParrottHyp z)

theorem polarVZMod_conj_eq (σ : ↥(H z)) (u w : QuotientV.V z) :
    polarVZMod h (conjV h σ u) (conjV h σ w) = polarVZMod h u w := by
  have h1 := qVZMod_mul_add h (conjV h σ u) (conjV h σ w)
  rw [← map_mul, qVZMod_conj, qVZMod_conj, qVZMod_conj] at h1
  have h2 := qVZMod_mul_add h u w
  set A := qVZMod h u
  set B := qVZMod h w
  set C := polarVZMod h (conjV h σ u) (conjV h σ w)
  set D := polarVZMod h u w
  have h1' : A + (B + C) = qVZMod h (u * w) := by
    rw [← add_assoc]
    exact h1.symm
  have h2' : A + (B + D) = qVZMod h (u * w) := by
    rw [← add_assoc]
    exact h2.symm
  have h4 : A + (B + C) = A + (B + D) := h1'.trans h2'.symm
  exact add_left_cancel (add_left_cancel h4)

theorem polarVZMod_conj_eq_of_fixed {σ : ↥(H z)} {u : QuotientV.V z}
    (hu : conjV h σ u = u) (w : QuotientV.V z) :
    polarVZMod h u (conjV h σ w) = polarVZMod h u w := by
  have hσinv : conjV h σ⁻¹ u = u := by
    rw [map_inv]
    apply (conjV h σ).injective
    rw [MulAut.apply_inv_self, hu]
  have hiso := polarVZMod_conj_eq (h := h) σ (conjV h σ⁻¹ u) w
  rw [hσinv, hu] at hiso
  exact hiso

theorem commutatorVSubmodule_le_orthogonal {σ : ↥(H z)} (hσ : orderOf σ = 3) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    commutatorVSubmodule h σ ≤
      (commutatorBilinForm h).orthogonal (fixSubmodule h σ) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  rw [← range_VComplementLinearMap (h := h) hσ] at hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  have hy : VComplementLinearMap h σ y =
      Additive.ofMul (VComplementHom h σ (Additive.toMul y)) := rfl
  rw [hy]
  change polarVZMod h (Additive.toMul u)
    (VComplementHom h σ (Additive.toMul y)) = 0
  rw [VComplementHom_apply, polarVZMod_add_right]
  have hu' : Additive.toMul u ∈ autFixedSubgroup (conjV h σ) :=
    (mem_fixSubmodule_iff h σ u).mp hu
  rw [mem_autFixedSubgroup] at hu'
  have hiso := polarVZMod_conj_eq_of_fixed (h := h) (σ := σ) hu' (Additive.toMul y)
  rw [hiso]
  calc polarVZMod h (Additive.toMul u) (Additive.toMul y) +
        polarVZMod h (Additive.toMul u) (Additive.toMul y)
      = 2 * polarVZMod h (Additive.toMul u) (Additive.toMul y) := (two_mul _).symm
    _ = 0 := by rw [show (2 : ZMod 2) = 0 by exact ZMod.natCast_self 2, zero_mul]

theorem finrank_commutatorVSubmodule {σ : ↥(H z)} (hσ : orderOf σ = 3) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Module.finrank (ZMod 2) (commutatorVSubmodule h σ) = 8 - fixDimV h σ := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  haveI : FiniteDimensional (ZMod 2) (Additive (QuotientV.V z)) := by
    apply FiniteDimensional.of_finrank_pos
    rw [finrank_addV h]
    norm_num
  rw [← range_VComplementLinearMap (h := h) hσ]
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (VComplementLinearMap h σ)) =
      fixDimV h σ := by
    rw [ker_VComplementLinearMap (h := h) hσ]
    rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker (VComplementLinearMap h σ)
  rw [finrank_addV h, hker] at hrn
  omega

theorem finrank_orthogonal_fixSubmodule {σ : ↥(H z)} :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Module.finrank (ZMod 2) ((commutatorBilinForm h).orthogonal (fixSubmodule h σ)) =
      8 - fixDimV h σ := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  haveI : FiniteDimensional (ZMod 2) (Additive (QuotientV.V z)) := by
    apply FiniteDimensional.of_finrank_pos
    rw [finrank_addV h]
    norm_num
  rw [LinearMap.BilinForm.finrank_orthogonal (commutatorBilinForm_nondegenerate h),
    finrank_addV h]
  rfl

theorem commutatorV_eq_orthogonal_fixSubmodule (h : Tim79a.ParrottHyp z)
    (σ : ↥(H z)) (hσ : orderOf σ = 3) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    commutatorVSubmodule h σ =
      (commutatorBilinForm h).orthogonal (fixSubmodule h σ) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  haveI : FiniteDimensional (ZMod 2) (Additive (QuotientV.V z)) := by
    apply FiniteDimensional.of_finrank_pos
    rw [finrank_addV h]
    norm_num
  exact Submodule.eq_of_le_of_finrank_eq (commutatorVSubmodule_le_orthogonal h hσ)
    (by rw [finrank_commutatorVSubmodule h hσ, finrank_orthogonal_fixSubmodule h])

end Orthogonal

section Equality

variable (h : Tim79a.ParrottHyp z)


end Equality

section J0Normal

variable (h : Tim79a.ParrottHyp z)

theorem mem_J0sub_inclusion_iff (j : J z) :
    (Subgroup.inclusion (J_le_H (z := z)) j : ↥(H z)) ∈ J0sub (z := z) (D := D) ↔
      j ∈ centralizerJ (sigma1Nine (z := z) D) := by
  rw [mem_J0sub_iff']
  constructor
  · rintro ⟨-, hcomm⟩
    exact mem_centralizerJ_iff.mpr hcomm
  · intro hj
    exact ⟨j.2, mem_centralizerJ_iff.mp hj⟩

theorem centralizerJ_conj_eq_of_J0sub_normal
    (hJ0 : (J0sub (z := z) (D := D)).Normal) (g : ↥(H z)) :
    centralizerJ (g * sigma1Nine (z := z) D * g⁻¹) =
      centralizerJ (sigma1Nine (z := z) D) := by
  ext j
  rw [mem_centralizerJ_iff, mem_centralizerJ_iff]
  have hconj_iff :
      ((conjJ' z g⁻¹ j : J z) : G) * (sigma1Nine (z := z) D : G) =
        (sigma1Nine (z := z) D : G) * ((conjJ' z g⁻¹ j : J z) : G) ↔
      (j : G) * ((g * sigma1Nine (z := z) D * g⁻¹ : ↥(H z)) : G) =
        ((g * sigma1Nine (z := z) D * g⁻¹ : ↥(H z)) : G) * (j : G) := by
    rw [conjJ'_apply_coe]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    constructor
    · intro hc
      calc (j : G) * (((g : G) * (sigma1Nine (z := z) D : G)) * (g : G)⁻¹)
          = (g : G) * (((g : G)⁻¹ * (j : G) * (g : G)) *
              (sigma1Nine (z := z) D : G)) * (g : G)⁻¹ := by group
        _ = (g : G) * ((sigma1Nine (z := z) D : G) *
              ((g : G)⁻¹ * (j : G) * (g : G))) * (g : G)⁻¹ := by rw [hc]
        _ = (((g : G) * (sigma1Nine (z := z) D : G)) * (g : G)⁻¹) * (j : G) := by group
    · intro hc
      calc ((g : G)⁻¹ * (j : G) * (g : G)) * (sigma1Nine (z := z) D : G)
          = (g : G)⁻¹ * ((j : G) * (((g : G) * (sigma1Nine (z := z) D : G)) *
              (g : G)⁻¹)) * (g : G) := by group
        _ = (g : G)⁻¹ * ((((g : G) * (sigma1Nine (z := z) D : G)) *
              (g : G)⁻¹) * (j : G)) * (g : G) := by rw [hc]
        _ = (sigma1Nine (z := z) D : G) * ((g : G)⁻¹ * (j : G) * (g : G)) := by group
  have hnorm_iff :
      (conjJ' z g⁻¹ j) ∈ centralizerJ (sigma1Nine (z := z) D) ↔
        j ∈ centralizerJ (sigma1Nine (z := z) D) := by
    have hmem : (Subgroup.inclusion (J_le_H (z := z)) j : ↥(H z)) ∈
        J0sub (z := z) (D := D) ↔
        (Subgroup.inclusion (J_le_H (z := z)) (conjJ' z g⁻¹ j) : ↥(H z)) ∈
          J0sub (z := z) (D := D) := by
      constructor
      · intro hj
        have hconj := hJ0.conj_mem
          (Subgroup.inclusion (J_le_H (z := z)) j) hj (g⁻¹)
        have hcoe : (g⁻¹ : ↥(H z)) * (Subgroup.inclusion (J_le_H (z := z)) j) *
            ((g⁻¹ : ↥(H z)))⁻¹ =
            (Subgroup.inclusion (J_le_H (z := z)) (conjJ' z g⁻¹ j) : ↥(H z)) := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
            conjJ'_apply_coe, inv_inv]
        rwa [hcoe] at hconj
      · intro hj
        have hconj := hJ0.conj_mem
          (Subgroup.inclusion (J_le_H (z := z)) (conjJ' z g⁻¹ j)) hj g
        have hcoe : (g : ↥(H z)) *
            (Subgroup.inclusion (J_le_H (z := z)) (conjJ' z g⁻¹ j)) *
            (g : ↥(H z))⁻¹ =
            (Subgroup.inclusion (J_le_H (z := z)) j : ↥(H z)) := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
            conjJ'_apply_coe, inv_inv]
          group
        rwa [hcoe] at hconj
    rw [← mem_J0sub_inclusion_iff (z := z) (D := D) (conjJ' z g⁻¹ j),
      ← mem_J0sub_inclusion_iff (z := z) (D := D) j]
    exact hmem.symm
  constructor
  · intro hc
    exact mem_centralizerJ_iff.mp
      (hnorm_iff.mp (mem_centralizerJ_iff.mpr (hconj_iff.mpr hc)))
  · intro hc
    exact hconj_iff.mp
      (mem_centralizerJ_iff.mp (hnorm_iff.mpr (mem_centralizerJ_iff.mpr hc)))

end J0Normal

section NormalFromJ0


end NormalFromJ0

section Q8


end Q8

end CFSG.RankThree.GF2n.Parrott
