module

public import CFSG.GH74.GLS.IVK.L2.BNMatrices
public import CFSG.GH74.GLS.IVK.L2.BNRankOne

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Pointwise

namespace L2BN

variable {F : Type} [Field F]

section Groups

noncomputable abbrev BB (H₁ : Subgroup (GL (Fin 2) F)) : Subgroup (GL (Fin 2) F) :=
  normalizer (((uHom F).range : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) ⊓ H₁

noncomputable abbrev DD (H₁ : Subgroup (GL (Fin 2) F)) : Subgroup (GL (Fin 2) F) :=
  diagGL F ⊓ H₁

noncomputable abbrev NN (H₁ : Subgroup (GL (Fin 2) F)) : Subgroup (GL (Fin 2) F) :=
  normalizer ((DD H₁ : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) ⊓ H₁

variable {H₁ : Subgroup (GL (Fin 2) F)}

theorem BB_le_H₁ : BB H₁ ≤ H₁ := inf_le_right


theorem mem_DD_of {g : GL (Fin 2) F} (h1 : g ∈ diagGL F) (h2 : g ∈ H₁) : g ∈ DD H₁ :=
  Subgroup.mem_inf.2 ⟨h1, h2⟩

theorem uT_mem_H₁ (hH : StatedSL 2 F ≤ H₁) (t : F) : uT t ∈ H₁ := hH (uT_mem_statedSL t)

theorem wGL_mem_H₁ (hH : StatedSL 2 F ≤ H₁) : wGL F ∈ H₁ := hH wGL_mem_statedSL

theorem U_le_H₁ (hH : StatedSL 2 F ≤ H₁) : (uHom F).range ≤ H₁ := fun g hg => by
  obtain ⟨t, rfl⟩ := (mem_range_uHom_iff' g).1 hg
  exact uT_mem_H₁ hH t

theorem U_le_B (hH : StatedSL 2 F ≤ H₁) : (uHom F).range ≤ BB H₁ :=
  le_inf Subgroup.le_normalizer (U_le_H₁ hH)

theorem D_le_B : DD H₁ ≤ BB H₁ := fun _ hg => ⟨diag_mem_normalizer_U hg.1, hg.2⟩


theorem B_c_zero {g : GL (Fin 2) F} (hg : g ∈ BB H₁) : g.1 1 0 = 0 :=
  c_eq_zero_of_mem_normalizer_U hg.1

theorem uT_inv_mul_aux (s : F) (g : GL (Fin 2) F) : g = uT s * (uT (-s) * g) := by
  rw [← mul_assoc, uT_mul, add_neg_cancel, uT_zero, one_mul]

theorem mem_B_of_c_zero (hH : StatedSL 2 F ≤ H₁) {g : GL (Fin 2) F} (hgH : g ∈ H₁)
    (hg : g.1 1 0 = 0) : g ∈ BB H₁ := by
  have hδ : uT (-(g.1 0 1 / g.1 1 1)) * g ∈ DD H₁ :=
    mem_DD_of (upper_decomp_left hg) (mul_mem (uT_mem_H₁ hH _) hgH)
  rw [uT_inv_mul_aux (g.1 0 1 / g.1 1 1) g]
  exact mul_mem (U_le_B hH (uT_mem_range _)) (D_le_B hδ)

theorem B_eq (hH : StatedSL 2 F ≤ H₁) : BB H₁ = (uHom F).range ⊔ DD H₁ := by
  apply le_antisymm
  · intro g hg
    have hδ : uT (-(g.1 0 1 / g.1 1 1)) * g ∈ DD H₁ :=
      mem_DD_of (upper_decomp_left (B_c_zero hg)) (mul_mem (uT_mem_H₁ hH _) (BB_le_H₁ hg))
    rw [uT_inv_mul_aux (g.1 0 1 / g.1 1 1) g]
    exact mul_mem (Subgroup.mem_sup_left (uT_mem_range _)) (Subgroup.mem_sup_right hδ)
  · exact sup_le (U_le_B hH) D_le_B


theorem w_mem_N (hH : StatedSL 2 F ≤ H₁) : wGL F ∈ NN H₁ := by
  refine Subgroup.mem_inf.2 ⟨?_, wGL_mem_H₁ hH⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hw := wGL_mem_H₁ hH
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← wGL_conj_mem_diagGL_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, mul_mem (mul_mem hw h2) (inv_mem hw)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := mul_mem (mul_mem (inv_mem hw) h2) hw
    simpa [mul_assoc] using this


theorem bruhat (hH : StatedSL 2 F ≤ H₁) {g : GL (Fin 2) F} (hg : g ∈ H₁) :
    g ∈ BB H₁ ∨ ∃ b₁ ∈ BB H₁, ∃ b₂ ∈ BB H₁, g = b₁ * wGL F * b₂ := by
  by_cases hc : g.1 1 0 = 0
  · exact Or.inl (mem_B_of_c_zero hH hg hc)
  · right
    obtain ⟨s, s', m, hgm, hm00, hm11⟩ := bruhat_core hc
    have hmH : m ∈ H₁ := by
      have : m = (uT s)⁻¹ * g * (uT s')⁻¹ := by
        rw [hgm]
        group
      rw [this]
      exact mul_mem (mul_mem (inv_mem (uT_mem_H₁ hH s)) hg) (inv_mem (uT_mem_H₁ hH s'))
    have hδ : m * (wGL F)⁻¹ ∈ DD H₁ :=
      mem_DD_of (mul_wGL_inv_mem_diagGL hm00 hm11)
        (mul_mem hmH (inv_mem (wGL_mem_H₁ hH)))
    refine ⟨uT s * (m * (wGL F)⁻¹), mul_mem (U_le_B hH (uT_mem_range s)) (D_le_B hδ), uT s',
      U_le_B hH (uT_mem_range s'), ?_⟩
    rw [hgm]
    group


theorem four_mem (hH : StatedSL 2 F ≤ H₁) {u : GL (Fin 2) F} (hu : u ∈ (uHom F).range)
    (hu1 : u ≠ 1) :
    wGL F * u * (wGL F)⁻¹ ∈ (BB H₁ : Set (GL (Fin 2) F)) * {wGL F} *
      (((uHom F).range : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) := by
  obtain ⟨t, rfl⟩ := (mem_range_uHom_iff' u).1 hu
  have ht : t ≠ 0 := fun h => hu1 (by rw [h, uT_zero])
  rw [four_identity ht]
  have hd : dg (Units.mk0 t ht)⁻¹ (Units.mk0 t ht) ∈ DD H₁ :=
    mem_DD_of (dg_mem_diagGL _ _) (hH (dg_mem_statedSL (by simp [ht])))
  exact ⟨_, ⟨uT (-t⁻¹) * dg (Units.mk0 t ht)⁻¹ (Units.mk0 t ht),
    mul_mem (U_le_B hH (uT_mem_range _)) (D_le_B hd), wGL F, rfl, rfl⟩,
    uT (-t⁻¹), uT_mem_range _, rfl⟩

end Groups

section Assembly

variable {H₁ : Subgroup (GL (Fin 2) F)}

def wH (hH : StatedSL 2 F ≤ H₁) : ↥H₁ := ⟨wGL F, wGL_mem_H₁ hH⟩

def wN (hH : StatedSL 2 F ≤ H₁) : ↥((NN H₁).subgroupOf H₁) :=
  ⟨wH hH, Subgroup.mem_subgroupOf.2 (w_mem_N hH)⟩


end Assembly

end L2BN


end CFSG.GH74.GLS.IVK
