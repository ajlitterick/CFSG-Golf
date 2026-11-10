module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4ModType
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.FieldFour
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.LieType.Ree Matrix

variable (K : Type) [Field K] [Finite K] [CharP K 2]

instance : CharP K ReeTag.F4.prime := inferInstanceAs (CharP K 2)

@[expose] def permF4 (i : Fin Tag.F4.rank) : Fin Tag.F4.rank := ReeTag.F4.perm i

@[expose] def expF4 (i : Fin Tag.F4.rank) : ℕ := ReeTag.F4.exponent i

theorem permF4_permF4 (i : Fin Tag.F4.rank) : permF4 (permF4 i) = i := by
  revert i; decide

theorem expF4_eq (i : Fin Tag.F4.rank) : expF4 i = if i.val ≤ 1 then 1 else 2 := by
  revert i; decide

@[expose] def phiF4 : MulAut (adjointGroup Tag.F4 K) := ReeTag.F4.finiteExceptionalAut K

theorem phi_xC (i : Fin Tag.F4.rank) (c : K) :
    phiF4 K (xC Tag.F4 K i c) = xC Tag.F4 K (permF4 i) (c ^ expF4 i) :=
  ReeTag.finiteExceptionalAut_xElement (t := ReeTag.F4) i c

theorem phi_yC (i : Fin Tag.F4.rank) (c : K) :
    phiF4 K (yC Tag.F4 K i c) = yC Tag.F4 K (permF4 i) (c ^ expF4 i) :=
  ReeTag.finiteExceptionalAut_yElement (t := ReeTag.F4) i c

theorem phi_wC (i : Fin Tag.F4.rank) (t : Kˣ) :
    phiF4 K (wC K i t) = wC K (permF4 i) (t ^ expF4 i) := by
  rw [wC_eq, wC_eq, map_mul, map_mul, phi_xC, phi_yC]
  have h : (-((t⁻¹ : Kˣ) : K)) ^ expF4 i = -((((t ^ expF4 i)⁻¹ : Kˣ)) : K) := by
    simp only [CharTwo.neg_eq, inv_pow, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rw [h]
  simp only [Units.val_pow_eq_pow_val]

theorem neg_one_unit : (-1 : Kˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])

theorem phi_dC (i : Fin Tag.F4.rank) (t : Kˣ) :
    phiF4 K (dC Tag.F4 K i t) = dC Tag.F4 K (permF4 i) (t ^ expF4 i) := by
  rw [dC_eq_wC, dC_eq_wC, map_mul, phi_wC, phi_wC, neg_one_unit, one_pow]

abbrev DF4 : CurtisDatum (adjointGroup Tag.F4 K) (coxeterSystem Tag.F4) 2 :=
  chevDatum Tag.F4 K 2 exists_weyl_neg_F4'

theorem phi_map_U : (DF4 K).U.map (phiF4 K).toMonoidHom = (DF4 K).U := by
  have h0 : ReeTag.F4.finiteReeAut K 0 = ReeTag.F4.finiteExceptionalAut K := by
    simp [ReeTag.finiteReeAut]
  have := ReeTag.map_finiteReeAut_posUnipotentSub (t := ReeTag.F4) (K := K) (a := 0)
  rw [h0] at this
  exact this

theorem phi_mem_U {u : adjointGroup Tag.F4 K} (hu : u ∈ (DF4 K).U) : phiF4 K u ∈ (DF4 K).U := by
  rw [← phi_map_U K]
  exact ⟨u, hu, rfl⟩

theorem H_le_of_dC {E : Subgroup (adjointGroup Tag.F4 K)} (hE : ∀ i (t : Kˣ), dC Tag.F4 K i t ∈ E) :
    (DF4 K).H ≤ E := by
  intro h hh
  have hh' : (h : ModGL Tag.F4 K) ∈ torusGroup Tag.F4 K := hh
  have hle : torusGroup Tag.F4 K ≤ E.map (adjointGroup Tag.F4 K).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact ⟨dC Tag.F4 K i t, hE i t, rfl⟩
  obtain ⟨e, he, he1⟩ := hle hh'
  have : e = h := Subtype.ext he1
  rwa [this] at he

theorem unit_pow_surj (i : Fin Tag.F4.rank) (t : Kˣ) : ∃ s : Kˣ, s ^ expF4 i = t := by
  obtain ⟨c, hc⟩ := finiteExceptionalAut_pow_exponent_surjective (K := K) ReeTag.F4 i (t : K)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : (0 : K) ^ expF4 i = (t : K) := hc
    have h1 : expF4 i ≠ 0 := by rw [expF4_eq]; split_ifs <;> omega
    rw [zero_pow h1] at this
    exact t.ne_zero this.symm
  have hc' : c ^ expF4 i = (t : K) := hc
  exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hc')⟩

theorem phi_mem_H {h : adjointGroup Tag.F4 K} (hh : h ∈ (DF4 K).H) : phiF4 K h ∈ (DF4 K).H := by
  have : (DF4 K).H ≤ (DF4 K).H.comap (phiF4 K).toMonoidHom :=
    H_le_of_dC K fun i t => by
      change phiF4 K (dC Tag.F4 K i t) ∈ (DF4 K).H
      rw [phi_dC]
      exact dC_mem_H _ _
  exact this hh


theorem pow_exp_bijective (i : Fin Tag.F4.rank) : Function.Bijective fun c : K => c ^ expF4 i := by
  have hs : Function.Surjective fun c : K => c ^ expF4 i :=
    finiteExceptionalAut_pow_exponent_surjective (K := K) ReeTag.F4 i
  exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩

theorem phi_nC (i : Fin Tag.F4.rank) : phiF4 K (nC Tag.F4 K i) = nC Tag.F4 K (permF4 i) := by
  rw [nC_eq_wC, nC_eq_wC, phi_wC, one_pow]

theorem phi_xC_nC (i : Fin Tag.F4.rank) (c : K) :
    phiF4 K (xC Tag.F4 K i c * nC Tag.F4 K i) =
      xC Tag.F4 K (permF4 i) (c ^ expF4 i) * nC Tag.F4 K (permF4 i) := by
  rw [map_mul, phi_xC, phi_nC]

section Transport

variable {V : Type} [AddCommGroup V] [Module K V]

theorem isChevType_comp_phi (ρ : Representation K (adjointGroup Tag.F4 K) V) (y : V)
    (χ : adjointGroup Tag.F4 K → K) (J : Finset (Fin Tag.F4.rank))
    (ht : IsChevType Tag.F4 K 2 exists_weyl_neg_F4' ρ y χ J)
    (χ' : adjointGroup Tag.F4 K → K)
    (hχ' : ∀ h ∈ (DF4 K).H, (ρ.comp (phiF4 K).toMonoidHom) h y = χ' h • y) :
    IsChevType Tag.F4 K 2 exists_weyl_neg_F4' (ρ.comp (phiF4 K).toMonoidHom) y χ'
      (Finset.univ.filter fun i => permF4 i ∈ J) := by
  classical
  obtain ⟨hfix, hy0, hH, hJ⟩ := ht
  have hchi : ∀ (i : Fin Tag.F4.rank) (t : Kˣ),
      χ' (dC Tag.F4 K i t) = χ (dC Tag.F4 K (permF4 i) (t ^ expF4 i)) := by
    intro i t
    have h1 := hχ' _ (dC_mem_H i t)
    have h2 := hH _ (dC_mem_H (permF4 i) (t ^ expF4 i))
    have h3 : (ρ.comp (phiF4 K).toMonoidHom) (dC Tag.F4 K i t) y =
        ρ (dC Tag.F4 K (permF4 i) (t ^ expF4 i)) y := by
      change ρ (phiF4 K (dC Tag.F4 K i t)) y = _
      rw [phi_dC]
    rw [h3, h2] at h1
    exact (smul_left_injective K hy0 h1).symm
  refine ⟨fun u hu => hfix (phiF4 K u) (phi_mem_U K hu), hy0, hχ', fun i => ?_⟩
  have hall : (∀ t : Kˣ, χ' (dC Tag.F4 K i t) = 1) ↔
      (∀ s : Kˣ, χ (dC Tag.F4 K (permF4 i) s) = 1) := by
    constructor
    · intro h s
      obtain ⟨t, ht⟩ := unit_pow_surj K i s
      have := h t
      rwa [hchi, ht] at this
    · intro h t
      rw [hchi]
      exact h _
  have hT : (DF4 K).heckeT (ρ.comp (phiF4 K).toMonoidHom) i y = (DF4 K).heckeT ρ (permF4 i) y := by
    have := Fintype.ofFinite K
    rw [heckeT_chevDatum, heckeT_chevDatum]
    have hb := (pow_exp_bijective K i).sum_comp
      (fun c : K => ρ (xC Tag.F4 K (permF4 i) c * nC Tag.F4 K (permF4 i)) y)
    rw [← hb]
    refine Finset.sum_congr rfl fun c _ => ?_
    change ρ (phiF4 K (xC Tag.F4 K i c * nC Tag.F4 K i)) y = _
    rw [phi_xC_nC]
  rw [Finset.mem_filter, hall, hT]
  simp only [Finset.mem_univ, true_and]
  exact hJ (permF4 i)

end Transport

@[expose] def m26Phi (k : ℕ) : Representation K (adjointGroup Tag.F4 K) (Idx26 → K) :=
  (m26Rep K).comp (phiF4 K ^ k).toMonoidHom

theorem m26Phi_apply (k : ℕ) (g : adjointGroup Tag.F4 K) :
    m26Phi K k g = m26Rep K ((phiF4 K ^ k) g) := rfl

theorem m26Phi_succ (k : ℕ) :
    m26Phi K (k + 1) = (m26Phi K k).comp (phiF4 K).toMonoidHom := by
  ext g : 1
  rw [m26Phi_apply]
  change m26Rep K ((phiF4 K ^ k * phiF4 K) g) = _
  rfl

theorem phiPow_mem_H (k : ℕ) {h : adjointGroup Tag.F4 K} (hh : h ∈ (DF4 K).H) :
    (phiF4 K ^ k) h ∈ (DF4 K).H := by
  induction k generalizing h with
  | zero => simpa using hh
  | succ k ih =>
    have := ih (phi_mem_H K hh)
    rwa [pow_succ]

@[expose] def nodeK (k : ℕ) : Fin Tag.F4.rank := if k % 2 = 0 then j3 else ⟨0, by decide⟩

theorem permF4_nodeK (k : ℕ) : permF4 (nodeK k) = nodeK (k + 1) := by
  unfold nodeK
  by_cases h : k % 2 = 0
  · have h' : ¬ (k + 1) % 2 = 0 := by omega
    rw [if_pos h, if_neg h']; decide
  · have h' : (k + 1) % 2 = 0 := by omega
    rw [if_neg h, if_pos h']; decide

theorem exists_chi_m26Phi (k : ℕ) :
    ∃ χ : adjointGroup Tag.F4 K → K, ∀ h ∈ (DF4 K).H, m26Phi K k h (y26 K) = χ h • y26 K := by
  classical
  refine ⟨fun h => if hh : h ∈ (DF4 K).H then (m26Rep_H_scalar K (phiPow_mem_H K k hh)).choose
    else 0, fun h hh => ?_⟩
  show m26Phi K k h (y26 K) = (if hh : h ∈ (DF4 K).H then
    (m26Rep_H_scalar K (phiPow_mem_H K k hh)).choose else 0) • y26 K
  rw [dif_pos hh, m26Phi_apply]
  exact (m26Rep_H_scalar K (phiPow_mem_H K k hh)).choose_spec

theorem m26Phi_isChevType (k : ℕ) (χ : adjointGroup Tag.F4 K → K)
    (hχ : ∀ h ∈ (DF4 K).H, m26Phi K k h (y26 K) = χ h • y26 K) :
    IsChevType Tag.F4 K 2 exists_weyl_neg_F4' (m26Phi K k) (y26 K) χ
      (Finset.univ.erase (nodeK k)) := by
  classical
  induction k generalizing χ with
  | zero =>
    have h0 : m26Phi K 0 = m26Rep K := by
      ext g : 1; simp [m26Phi_apply]
    rw [h0] at hχ ⊢
    simpa [nodeK, j3] using m26_isChevType K χ hχ
  | succ k ih =>
    obtain ⟨χk, hχk⟩ := exists_chi_m26Phi K k
    have h1 := ih χk hχk
    rw [m26Phi_succ] at hχ ⊢
    have h2 := isChevType_comp_phi K (m26Phi K k) (y26 K) χk _ h1 χ hχ
    convert h2 using 2
    ext i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter, ne_eq, true_and]
    rw [← permF4_nodeK]
    constructor
    · intro h h'
      exact h (by rw [← h', permF4_permF4])
    · intro h h'
      exact h (by rw [h', permF4_permF4])

theorem exp_mul_exp_perm (i : Fin Tag.F4.rank) : expF4 i * expF4 (permF4 i) = 2 := by
  revert i; decide

theorem phiSq_dC (i : Fin Tag.F4.rank) (t : Kˣ) :
    (phiF4 K ^ 2) (dC Tag.F4 K i t) = dC Tag.F4 K i (t ^ 2) := by
  have h : (phiF4 K ^ 2) (dC Tag.F4 K i t) = phiF4 K (phiF4 K (dC Tag.F4 K i t)) := by
    rw [pow_two]; rfl
  rw [h, phi_dC, phi_dC, permF4_permF4, ← pow_mul, exp_mul_exp_perm]

theorem phiPow_even_dC (m : ℕ) (i : Fin Tag.F4.rank) (t : Kˣ) :
    (phiF4 K ^ (2 * m)) (dC Tag.F4 K i t) = dC Tag.F4 K i (t ^ 2 ^ m) := by
  induction m generalizing t with
  | zero => simp
  | succ m ih =>
    have h : phiF4 K ^ (2 * (m + 1)) = phiF4 K ^ (2 * m) * phiF4 K ^ 2 := by
      rw [← pow_add]; congr 1
    rw [h, MulAut.mul_apply, phiSq_dC, ih, ← pow_mul, pow_succ, mul_comm]

theorem phiPow_odd_dC (m : ℕ) (i : Fin Tag.F4.rank) (t : Kˣ) :
    (phiF4 K ^ (2 * m + 1)) (dC Tag.F4 K i t) =
      dC Tag.F4 K (permF4 i) ((t ^ expF4 i) ^ 2 ^ m) := by
  have h : phiF4 K ^ (2 * m + 1) = phiF4 K ^ (2 * m) * phiF4 K := by rw [pow_succ]
  rw [h, MulAut.mul_apply, phi_dC, phiPow_even_dC]

theorem m26Rep_dC_scalar (c : K) (j : Fin Tag.F4.rank) (s : Kˣ)
    (h : m26Rep K (dC Tag.F4 K j s) (y26 K) = c • y26 K) :
    c = (s : K) ^ (if j.val = 3 then 1 else 0) := by
  rw [torus_act] at h
  exact (smul_left_injective K (y26_ne_zero K) h).symm

theorem permF4_val_eq_three (i : Fin Tag.F4.rank) : (permF4 i).val = 3 ↔ i.val = 0 := by
  revert i; decide

theorem expF4_zero (i : Fin Tag.F4.rank) (h : i.val = 0) : expF4 i = 1 := by
  revert i; decide

theorem m26Phi_chi_even (m : ℕ) (χ : adjointGroup Tag.F4 K → K)
    (hχ : ∀ h ∈ (DF4 K).H, m26Phi K (2 * m) h (y26 K) = χ h • y26 K) (i : Fin Tag.F4.rank)
    (t : Kˣ) : χ (dC Tag.F4 K i t) = (t : K) ^ (if i.val = 3 then 2 ^ m else 0) := by
  have h1 := hχ _ (dC_mem_H i t)
  rw [m26Phi_apply, phiPow_even_dC] at h1
  have h2 := m26Rep_dC_scalar K _ i _ h1
  rw [h2, Units.val_pow_eq_pow_val, ← pow_mul]
  split_ifs <;> simp

theorem m26Phi_chi_odd (m : ℕ) (χ : adjointGroup Tag.F4 K → K)
    (hχ : ∀ h ∈ (DF4 K).H, m26Phi K (2 * m + 1) h (y26 K) = χ h • y26 K) (i : Fin Tag.F4.rank)
    (t : Kˣ) : χ (dC Tag.F4 K i t) = (t : K) ^ (if i.val = 0 then 2 ^ m else 0) := by
  have h1 := hχ _ (dC_mem_H i t)
  rw [m26Phi_apply, phiPow_odd_dC] at h1
  have h2 := m26Rep_dC_scalar K _ (permF4 i) _ h1
  rw [h2]
  by_cases hi : i.val = 0
  · rw [ite_eq_left ((permF4_val_eq_three i).2 hi), ite_eq_left hi, expF4_zero i hi, pow_one,
      Units.val_pow_eq_pow_val, pow_one]
  · rw [ite_eq_right (fun h => hi ((permF4_val_eq_three i).1 h)), ite_eq_right hi]
    simp

section Chars

variable {V₁ V₂ : Type} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]


end Chars

section IsoTwist

variable {V : Type} [AddCommGroup V] [Module K V]

theorem isSimpleRep_m26Phi (k : ℕ) : IsSimpleRep (m26Phi K k) := by
  have hs : Function.Surjective (phiF4 K ^ k).toMonoidHom := (phiF4 K ^ k).surjective
  exact (isSimpleRep_comp_iff (m26Rep K) hs).2 (isSimpleRep_m26 K)


end IsoTwist

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
