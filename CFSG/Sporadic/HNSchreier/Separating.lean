module

public import CFSG.Sporadic.HNSchreier.SchreierData
public import CFSG.Sporadic.HNSchreier.SepCheck
public import CFSG.Sporadic.HNSchreier.Algebra
public import CFSG.Certificates.Kernel.StabChainBot

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Sporadic.F5 CFSG.Sporadic.F5.Native CFSG.Sporadic.He.Native
open CFSG.Sporadic.HNSchreier.Native Matrix


theorem form_pres {C : Matrix (Fin 133) (Fin 133) (ZMod 5)} (hC : Cᵀ * formM * C = formM)
    (x y : Fin 133 → ZMod 5) : (C *ᵥ x) ⬝ᵥ (formM *ᵥ (C *ᵥ y)) = x ⬝ᵥ (formM *ᵥ y) := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hC]

theorem beta_eq (i j : X) : beta i j = vL i ⬝ᵥ (formM *ᵥ vL j) :=
  cert_hn_schreier_action_data.2.2.2.2.2.2.2.2.2.2.2.2.2 i j

theorem vL_a0 (i : X) : vL (a0 i) = matA *ᵥ vL i := by
  rw [a0_apply, ← (fam_hn_faithful_vector_orbit_action.2.2.2.1 i i.isLt).1]

theorem vL_a1 (i : X) : vL (a1 i) = matB *ᵥ vL i := by
  rw [a1_apply, ← (fam_hn_faithful_vector_orbit_action.2.2.2.1 i i.isLt).2]

@[expose] def betaStab : Subgroup (Equiv.Perm X) where
  carrier := {g | ∀ i j, beta (g i) (g j) = beta i j}
  mul_mem' {g h} hg hh i j := by
    show beta (g (h i)) (g (h j)) = beta i j
    rw [hg, hh]
  one_mem' i j := rfl
  inv_mem' {g} hg i j := by
    have := hg (g⁻¹ i) (g⁻¹ j)
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at this
    exact this.symm

theorem beta_invariant
    {g : Equiv.Perm X} (hg : g ∈ PH) (i j : X) :
    beta (g i) (g j) = beta i j := by
  have hle : PH ≤ betaStab := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · intro i j
      rw [beta_eq, beta_eq, vL_a0, vL_a0, form_pres form_parts.2.2.1]
    · intro i j
      rw [beta_eq, beta_eq, vL_a1, vL_a1, form_pres form_parts.2.2.2]
  exact hle hg i j


theorem baseIndex_lt' {k : ℕ} (hk : k < 22) : baseIndex k < hnsData.n := baseIndex_lt hk


abbrev baseX (k : Fin 22) : X := ⟨baseIndex k, baseIndex_lt' k.isLt⟩

theorem chainPt_eq : chainPt 0 = baseX 0 ∧ chainPt 1 = baseX 2 ∧ chainPt 2 = baseX 19 ∧
    chainPt 3 = baseX 1 := by
  decide +kernel

theorem eq_one_of_fix_chain
    {h : JH} (hfix : ∀ i < 4, h • chainPt i = chainPt i) : h = 1 := by
  obtain ⟨hcard, hL⟩ := level_cert
  have : Finite JH := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have htr := hns_pretransitive
  choose f hf using hL
  let P : ℕ → Finset X := fun i => match i with
    | 0 => Finset.univ
    | l + 1 => if hl : l < 3 then Finset.univ.image (fun k => f l hl k • chainPt (l + 1)) else ∅
  refine CFSG.KS.StabChain.eq_one_of_chain (G := JH) chainPt P 4 (fun i hi p hp => ?_) ?_ hfix
  · match i, hi, hp with
    | 0, _, _ => exact ⟨_, fun k hk => absurd hk (Nat.not_lt_zero k),
        (MulAction.exists_smul_eq JH (chainPt 0) p).choose_spec⟩
    | l + 1, hi, hp =>
      have hl : l < 3 := by omega
      simp only [P, dif_pos hl, Finset.mem_image] at hp
      obtain ⟨k, -, rfl⟩ := hp
      exact ⟨f l hl k, fun j hj => (hf l hl).1 k j (by omega), rfl⟩
  · have hc : ∀ l (hl : l < 3), (P (l + 1)).card = chainSizes.getD l 0 := by
      intro l hl
      simp only [P, dif_pos hl]
      rw [Finset.card_image_of_injective _ (hf l hl).2, Finset.card_univ, Fintype.card_fin]
    have h0 : (P 0).card = 1140000 := by
      simp only [P, Finset.card_univ, Fintype.card_fin]
      rfl
    rw [hcard, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_one, h0, hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num)]
    decide

theorem eq_one_of_fix_base
    {g : Equiv.Perm X} (hg : g ∈ PH) (hfix : ∀ k, g (baseX k) = baseX k) :
    g = 1 := by
  obtain ⟨h, hh⟩ := jEquivP.surjective ⟨g, hg⟩
  have e : ∀ x : X, h • x = g x := fun x => by
    rw [← jEquivP_apply h x, hh]
  have h1 : h = 1 := by
    refine eq_one_of_fix_chain fun i hi => ?_
    rw [e]
    obtain ⟨c0, c1, c2, c3⟩ := chainPt_eq
    interval_cases i
    · rw [c0]; exact hfix 0
    · rw [c1]; exact hfix 2
    · rw [c2]; exact hfix 19
    · rw [c3]; exact hfix 1
  have := congrArg Subtype.val hh
  rw [h1, map_one] at this
  exact this.symm


end CFSG.Sporadic.HNSchreier
