module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.PrincipalSeriesValues
public import CFSG.CharacterTheory.Wreathed.CentralSL2.Augmentation
public import CFSG.CharacterTheory.Wreathed.CentralSL2.CharacterTools

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section LinearTwist

variable {K : Type} [Group K] [Fintype K]

theorem linearTwist_mem_blocksIrr (χ : K →* ℂˣ) {θ : K → ℂ} (hθ : θ ∈ BlocksIrr K) :
    (fun g => (χ g : ℂ) * θ g) ∈ BlocksIrr K := by
  have hθθ : BlocksInnerProduct θ θ = 1 := by
    have h := blocksInnerProduct_irreducible ⟨θ, hθ⟩ ⟨θ, hθ⟩
    rw [ite_eq_left rfl] at h
    exact h
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hθ
  let ρ' : Representation ℂ K V :=
    { toFun := fun g => (χ g : ℂ) • ρ g
      map_one' := by simp
      map_mul' := fun g h => by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul] }
  have hchar : ρ'.character = fun g => (χ g : ℂ) * ρ.character g := by
    funext g
    change LinearMap.trace ℂ V ((χ g : ℂ) • ρ g) = _
    rw [map_smul, smul_eq_mul]
    rfl
  rw [← hchar]
  apply CFSG.Wreathed.mem_blocksIrr_of_norm_one ρ'
  rw [hchar]
  rw [← hθθ]
  unfold BlocksInnerProduct
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_mul, conj_units_hom]
  have h1 : (χ g : ℂ) * (χ g⁻¹ : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  linear_combination (ρ.character g * starRingEnd ℂ (ρ.character g)) * h1

end LinearTwist

section Irreducibility

variable (F : Type) [Field F] [Fintype F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

omit [Fintype F] in
theorem hom_eq_one_of_inv_eq_one {η : Fˣ →* ℂˣ} (h : η⁻¹ = 1) : η = 1 := by
  ext c
  have := DFunLike.congr_fun h c
  simpa using this

theorem ne_weylParameter (hb : ¬ IsSquare b) {P : PrincipalSeriesParameter F b m}
    (hP : P.1.1 ≠ 1) : P ≠ weylParameter F b m heven P :=
  fun h => hP ((weylParameter_eq_self_iff F b m heven hb P).mp h.symm)

omit [Fintype F] in
theorem weylParameter_ne_one {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1) :
    (weylParameter F b m heven P).1.1 ≠ 1 :=
  fun h => hP (hom_eq_one_of_inv_eq_one F h)

theorem principalSeries_one (lam : splitTorus F b m hm heven →* ℂˣ) :
    principalSeries F b m hm heven lam 1 = (Nat.card F : ℂ) + 1 := by
  have h := principalSeries_cyclicGenerator_sq_zpow F b m hm heven lam 0
  rw [zpow_zero, zpow_zero, mul_one] at h
  exact h

theorem principalSeries_mem_blocksIrr (hb : ¬ IsSquare b) (P : PrincipalSeriesParameter F b m)
    (hP : P.1.1 ≠ 1) :
    principalSeries F b m hm heven (torusCharacter F b m hm heven P) ∈
      BlocksIrr (CentralExtension F b m hm heven) := by
  have hlin : (fun g : borelSubgroup F b m hm heven =>
      (borelInflation F b m hm heven (torusCharacter F b m hm heven P) g : ℂ)) ∈
        BlocksIrr (borelSubgroup F b m hm heven) :=
    monoidHom_mem_blocksIrr ((Units.coeHom ℂ).comp
      (borelInflation F b m hm heven (torusCharacter F b m hm heven P)))
  obtain ⟨W, _, _, _, τ, hτ⟩ :=
    CFSG.Wreathed.exists_representation_inducedFunction (borelSubgroup F b m hm heven) hlin
  have hnorm : BlocksInnerProduct τ.character τ.character = 1 := by
    rw [hτ]
    change BlocksInnerProduct (principalSeries F b m hm heven (torusCharacter F b m hm heven P))
      (principalSeries F b m hm heven (torusCharacter F b m hm heven P)) = 1
    rw [principalSeries_inner_parameter, ite_eq_left rfl,
      ite_eq_right (ne_weylParameter F b m heven hb hP), add_zero]
  have h := CFSG.Wreathed.mem_blocksIrr_of_norm_one τ hnorm
  rw [hτ] at h
  exact h

theorem principalSeries_eq_iff (hb : ¬ IsSquare b) {P Q : PrincipalSeriesParameter F b m}
    (hP : P.1.1 ≠ 1) (hQ : Q.1.1 ≠ 1) :
    principalSeries F b m hm heven (torusCharacter F b m hm heven P) =
        principalSeries F b m hm heven (torusCharacter F b m hm heven Q) ↔
      Q = P ∨ Q = weylParameter F b m heven P := by
  have hPw := ne_weylParameter F b m heven hb hP
  constructor
  · intro h
    have h1 := principalSeries_inner_parameter F b m hm heven P Q
    rw [← h, principalSeries_inner_parameter, ite_eq_left rfl, ite_eq_right hPw] at h1
    by_contra hne
    obtain ⟨hne1, hne2⟩ := not_or.mp hne
    have hPQ : P ≠ Q := fun h => hne1 h.symm
    have hPwQ : P ≠ weylParameter F b m heven Q := fun h =>
      hne2 (by rw [h, weylParameter_involutive])
    rw [ite_eq_right hPQ, ite_eq_right hPwQ] at h1
    norm_num at h1
  · rintro (rfl | rfl)
    · rfl
    · have hirrP := principalSeries_mem_blocksIrr F b m hm heven hb P hP
      have hirrQ := principalSeries_mem_blocksIrr F b m hm heven hb _
        (weylParameter_ne_one F b m heven hP)
      have h1 := principalSeries_inner_parameter F b m hm heven P (weylParameter F b m heven P)
      rw [ite_eq_right hPw, weylParameter_involutive, ite_eq_left rfl, zero_add] at h1
      have h2 := blocksInnerProduct_irreducible ⟨_, hirrP⟩ ⟨_, hirrQ⟩
      change BlocksInnerProduct (principalSeries F b m hm heven (torusCharacter F b m hm heven P))
        (principalSeries F b m hm heven (torusCharacter F b m hm heven
          (weylParameter F b m heven P))) = _ at h2
      rw [h1] at h2
      by_contra hne
      rw [ite_eq_right (fun h => hne (congrArg Subtype.val h))] at h2
      norm_num at h2

end Irreducibility

section Count

variable (F : Type) [Field F] [Fintype F] (b : Fˣ) (m : ℕ)

theorem card_pow_eq (hm : 0 < m) (c : ℂˣ) : Nat.card {z : ℂˣ // z ^ m = c} = m := by
  obtain ⟨z₀, hz₀⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ) hm
  have hz0 : z₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hz₀
    exact c.ne_zero hz₀.symm
  let u₀ : ℂˣ := Units.mk0 z₀ hz0
  have hu₀ : u₀ ^ m = c := Units.ext (by simp [u₀, hz₀])
  have : NeZero m := ⟨hm.ne'⟩
  let e : {z : ℂˣ // z ^ m = c} ≃ rootsOfUnity m ℂ :=
    { toFun := fun z => ⟨z.1 * u₀⁻¹, by
        rw [mem_rootsOfUnity, mul_pow, z.2, inv_pow, hu₀, mul_inv_cancel]⟩
      invFun := fun ζ => ⟨ζ.1 * u₀, by
        rw [mul_pow, (mem_rootsOfUnity _ _).mp ζ.2, hu₀, one_mul]⟩
      left_inv := fun z => by
        apply Subtype.ext
        simp
      right_inv := fun ζ => by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Complex.card_rootsOfUnity]

theorem card_units_hom : Nat.card (Fˣ →* ℂˣ) = Nat.card F - 1 := by
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self Fˣ ℂ
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_units,
    Nat.card_eq_fintype_card]

theorem finite_units_hom : Finite (Fˣ →* ℂˣ) := by
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self Fˣ ℂ
  exact Finite.of_equiv _ e.toEquiv.symm

theorem card_principalSeriesParameter (hm : 0 < m) :
    Nat.card (PrincipalSeriesParameter F b m) = (Nat.card F - 1) * m := by
  have := finite_units_hom F
  have : Fintype (Fˣ →* ℂˣ) := Fintype.ofFinite _
  have hfin : ∀ η : Fˣ →* ℂˣ, Finite {z : ℂˣ // z ^ m = η (torusConstant F b m)} := fun η =>
    Nat.finite_of_card_ne_zero (by rw [card_pow_eq m hm]; exact hm.ne')
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    fun (η : Fˣ →* ℂˣ) (z : ℂˣ) => z ^ m = η (torusConstant F b m)), Nat.card_sigma]
  simp only [card_pow_eq m hm]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    card_units_hom]

omit [Fintype F] in
theorem card_principalSeriesParameter_trivial (hm : 0 < m) :
    Nat.card {P : PrincipalSeriesParameter F b m // P.1.1 = 1} = m := by
  let e : {P : PrincipalSeriesParameter F b m // P.1.1 = 1} ≃ {z : ℂˣ // z ^ m = 1} :=
    { toFun := fun P => ⟨P.1.1.2, by rw [P.1.2, P.2]; rfl⟩
      invFun := fun z => ⟨⟨(1, z.1), by rw [z.2]; rfl⟩, rfl⟩
      left_inv := fun P => by
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext P.2.symm rfl
      right_inv := fun z => rfl }
  rw [Nat.card_congr e, card_pow_eq m hm]

variable (hm : 0 < m) (heven : Even m)

theorem principalSeries_ncard (hb : ¬ IsSquare b) :
    Set.ncard ((fun P => principalSeries F b m hm heven (torusCharacter F b m hm heven P)) ''
      {P : PrincipalSeriesParameter F b m | P.1.1 ≠ 1}) = m * (Nat.card F - 2) / 2 := by
  have hcardP := card_principalSeriesParameter F b m hm
  have hfinP : Finite (PrincipalSeriesParameter F b m) := Nat.finite_of_card_ne_zero (by
    rw [hcardP]
    have : 2 ≤ Nat.card F := Finite.one_lt_card
    exact Nat.mul_ne_zero (by omega) hm.ne')
  have : Fintype (PrincipalSeriesParameter F b m) := Fintype.ofFinite _
  set f := fun P => principalSeries F b m hm heven (torusCharacter F b m hm heven P) with hf
  set s := Finset.univ.filter (fun P : PrincipalSeriesParameter F b m => P.1.1 ≠ 1) with hs
  have hset : {P : PrincipalSeriesParameter F b m | P.1.1 ≠ 1} = ↑s := by
    ext P
    simp [hs]
  have hfibre : ∀ y ∈ s.image f, (s.filter (fun P => f P = y)).card = 2 := by
    intro y hy
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hy
    have hP₀' : P₀.1.1 ≠ 1 := (Finset.mem_filter.mp hP₀).2
    have hpair : s.filter (fun P => f P = f P₀) = {P₀, weylParameter F b m heven P₀} := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, hs,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hQ, hfQ⟩
        exact (principalSeries_eq_iff F b m hm heven hb hP₀' hQ).mp hfQ.symm
      · rintro (rfl | rfl)
        · exact ⟨hP₀', rfl⟩
        · refine ⟨weylParameter_ne_one F b m heven hP₀', ?_⟩
          exact ((principalSeries_eq_iff F b m hm heven hb hP₀'
            (weylParameter_ne_one F b m heven hP₀')).mpr (Or.inr rfl)).symm
    rw [hpair, Finset.card_pair (ne_weylParameter F b m heven hb hP₀')]
  have h2 : s.card = 2 * (s.image f).card := by
    rw [Finset.card_eq_sum_card_image f s, Finset.sum_congr rfl hfibre, Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hcomp : s.card + (Finset.univ.filter
      (fun P : PrincipalSeriesParameter F b m => P.1.1 = 1)).card = (Nat.card F - 1) * m := by
    rw [← hcardP, Nat.card_eq_fintype_card, add_comm, hs]
    convert Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun P : PrincipalSeriesParameter F b m => P.1.1 = 1)
    exact Finset.card_univ.symm
  have htriv : (Finset.univ.filter
      (fun P : PrincipalSeriesParameter F b m => P.1.1 = 1)).card = m := by
    have h := card_principalSeriesParameter_trivial F b m hm
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    exact h
  rw [htriv] at hcomp
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h3 : (Nat.card F - 1) * m = m * (Nat.card F - 2) + m := by
    have : Nat.card F - 1 = (Nat.card F - 2) + 1 := by omega
    rw [this, add_mul, one_mul, mul_comm]
  have hs' : s.card = m * (Nat.card F - 2) := by omega
  rw [hset, ← Finset.coe_image, Set.ncard_coe_finset]
  omega

end Count

section TrivialCharacter

variable (F : Type) [Field F] [Fintype F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem steinberg_mem_blocksIrr :
    (fun g => fixedPointCount (CentralExtension F b m hm heven) (Omega F) g - 1) ∈
      BlocksIrr (CentralExtension F b m hm heven) := by
  have h2 := centralExtension_isMultiplyPretransitive F b m hm heven
  have ht : MulAction.IsPretransitive (CentralExtension F b m hm heven) (Omega F) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  exact ((permutation_character_orbit_count (CentralExtension F b m hm heven)
    (Omega F)).2.2.2 ht (two_le_card_omega F)).mp h2

theorem fixedPointCount_one :
    fixedPointCount (CentralExtension F b m hm heven) (Omega F) 1 = (Nat.card F : ℂ) + 1 := by
  have huniv : MulAction.fixedBy (Omega F) (1 : CentralExtension F b m hm heven) = Set.univ := by
    ext y
    simp
  rw [fixedPointCount, huniv, Nat.card_congr (Equiv.Set.univ _), card_omega]
  push_cast
  rfl


omit [Fintype F] in
theorem rootCharacter_baseResidue_quotientClass (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (r : ℕ)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    (rootCharacter m hm ζ hζ r (baseResidue F b m hm heven
      (quotientClass F b m hm heven X j)) : ℂ) = ζ ^ (r * j.val) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  rw [baseResidue_quotientClass]
  conv_lhs => rw [← ZMod.natCast_zmod_val j, map_natCast]
  exact rootCharacter_natCast m hm ζ hζ r j.val


end TrivialCharacter

section Projective


end Projective


end CFSG.Wreathed.CentralSL2
