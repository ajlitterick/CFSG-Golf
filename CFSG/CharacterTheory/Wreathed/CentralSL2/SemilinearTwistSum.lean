module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearTwistClifford
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearPrincipalSum

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Above

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] noncomputable def aboveFamily (Pf : Set (CentralExtension F b m hm heven → ℂ)) :
    Set (SemilinearExtension F b m hm heven Sigma hSigma → ℂ) :=
  {ξ | ξ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma) ∧
    ∃ θ ∈ Pf, liesAbove hSigma ξ θ}

theorem aboveFamily_finite (Pf : Set (CentralExtension F b m hm heven → ℂ)) :
    (aboveFamily hSigma Pf).Finite :=
  (CFSG.BlockSectionOrthogonality.Helpers.irreducibles_finite _).subset fun _ h => h.1


theorem degree_eq_card_above_twist (Pf : Finset (CentralExtension F b m hm heven → ℂ))
    (hirr : ∀ θ ∈ Pf, θ ∈ BlocksIrr (CentralExtension F b m hm heven))
    (hstable : ∀ θ ∈ Pf, ∀ σ : Sigma, fieldTwist hSigma σ θ ∈ Pf)
    {ξ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ}
    (hξ : ξ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma))
    {θ₀ : CentralExtension F b m hm heven → ℂ} (hθ₀ : θ₀ ∈ Pf) (habove : liesAbove hSigma ξ θ₀) :
    ξ 1 = θ₀ 1 * (Pf.filter fun θ => liesAbove hSigma ξ θ).card := by
  have hirr₀ := hirr θ₀ hθ₀
  obtain ⟨χ, hχ, hres⟩ := exists_inertia_extension (hm := hm) (heven := heven) hSigma hirr₀
  obtain ⟨hdeg, -, hiff, hrest, -⟩ := twist_clifford hSigma hirr₀ hχ hres
  obtain ⟨ρ, rfl⟩ := (hiff ξ hξ).mp habove
  obtain ⟨C, hC⟩ := CFSG.Wreathed.exists_leftCoset_reps (twistStabilizer hSigma θ₀)
  obtain ⟨hsum, hdist, hmult⟩ := hrest C hC
  have hfilter : Pf.filter (fun θ => liesAbove hSigma (twistInduced hSigma θ₀ χ ρ) θ) =
      C.image fun σ => fieldTwist hSigma σ θ₀ := by
    ext θ
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hθ, habove'⟩
      unfold liesAbove at habove'
      rw [hsum ρ, CFSG.Wreathed.blocksInnerProduct_finset_sum_left] at habove'
      by_contra hnot
      rw [Finset.sum_eq_zero fun σ hσ => by
        have hirrσ := fieldTwist_mem_blocksIrr hSigma hirr₀ σ
        have h3 := blocksInnerProduct_irreducible ⟨_, hirrσ⟩ ⟨_, hirr θ hθ⟩
        change BlocksInnerProduct (fieldTwist hSigma σ θ₀) θ = _ at h3
        rw [h3, ite_eq_right]
        intro heq
        exact hnot ⟨σ, hσ, congrArg Subtype.val heq⟩] at habove'
      exact lt_irrefl 0 habove'
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨hstable θ₀ hθ₀ σ, ?_⟩
      unfold liesAbove
      rw [hmult ρ σ hσ]
      exact one_pos
  rw [hfilter, Finset.card_image_of_injOn fun σ hσ σ' hσ' h => by
    by_contra hne
    exact hdist σ hσ σ' hσ' hne h, card_coset_reps _ C hC, (hdeg ρ).2]
  ring

theorem sum_degree_above_twist (Pf : Set (CentralExtension F b m hm heven → ℂ))
    {θ : CentralExtension F b m hm heven → ℂ} (hθPf : θ ∈ Pf)
    (hθ : θ ∈ BlocksIrr (CentralExtension F b m hm heven)) :
    ∑ ξ ∈ (aboveFamily_finite (hm := hm) (heven := heven) hSigma Pf).toFinset.filter
        (fun ξ => liesAbove hSigma ξ θ), ξ 1 = (Nat.card Sigma : ℂ) * θ 1 := by
  obtain ⟨χ, hχ, hres⟩ := exists_inertia_extension (hm := hm) (heven := heven) hSigma hθ
  obtain ⟨hdeg, hinj, hiff, -, -⟩ := twist_clifford hSigma hθ hχ hres
  have hcyc : IsCyclic (twistStabilizer hSigma θ) := by
    have : IsCyclic Sigma := fieldSubgroup_isCyclic F Sigma
    infer_instance
  let _ : CommGroup (twistStabilizer hSigma θ) := IsCyclic.commGroup
  have := finite_hom_units_of_isCyclic (twistStabilizer hSigma θ)
  have : Fintype (twistStabilizer hSigma θ →* ℂˣ) := Fintype.ofFinite _
  have hfilter : (aboveFamily_finite (hm := hm) (heven := heven) hSigma Pf).toFinset.filter
      (fun ξ => liesAbove hSigma ξ θ) = Finset.univ.image (twistInduced hSigma θ χ) := by
    ext ξ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hξ, habove⟩
      obtain ⟨ρ, rfl⟩ := (hiff ξ hξ.1).mp habove
      exact ⟨ρ, rfl⟩
    · rintro ⟨ρ, rfl⟩
      have habove : liesAbove hSigma (twistInduced hSigma θ χ ρ) θ :=
        (hiff _ (hdeg ρ).1).mpr ⟨ρ, rfl⟩
      exact ⟨⟨(hdeg ρ).1, θ, hθPf, habove⟩, habove⟩
  rw [hfilter, Finset.sum_image fun ρ _ ρ' _ h => hinj h]
  simp_rw [fun ρ => (hdeg ρ).2]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    card_hom_units_of_isCyclic, ← mul_assoc, ← Nat.cast_mul,
    Subgroup.card_mul_index (twistStabilizer hSigma θ)]

theorem sum_sq_aboveFamily (Pf : Finset (CentralExtension F b m hm heven → ℂ)) (D : ℂ)
    (hirr : ∀ θ ∈ Pf, θ ∈ BlocksIrr (CentralExtension F b m hm heven))
    (hdegPf : ∀ θ ∈ Pf, θ 1 = D)
    (hstable : ∀ θ ∈ Pf, ∀ σ : Sigma, fieldTwist hSigma σ θ ∈ Pf) :
    ∑ ξ ∈ (aboveFamily_finite (hm := hm) (heven := heven) hSigma ↑Pf).toFinset, ξ 1 ^ 2 =
      (Nat.card Sigma : ℂ) * D ^ 2 * Pf.card := by
  set famFin := (aboveFamily_finite (hm := hm) (heven := heven) hSigma ↑Pf).toFinset
    with hfamFin
  have hstep : ∀ ξ ∈ famFin, ξ 1 ^ 2 = D * ∑ θ ∈ Pf, if liesAbove hSigma ξ θ then ξ 1 else 0 := by
    intro ξ hξ
    rw [hfamFin, Set.Finite.mem_toFinset] at hξ
    obtain ⟨hξirr, θ₀, hθ₀, habove⟩ := hξ
    have hdeg := degree_eq_card_above_twist hSigma Pf hirr hstable hξirr hθ₀ habove
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hdeg' : ξ 1 = D * ((Pf.filter fun θ => liesAbove hSigma ξ θ).card) := by
      rw [hdeg, hdegPf θ₀ hθ₀]
    calc ξ 1 ^ 2 = ξ 1 * ξ 1 := sq _
      _ = D * ((Pf.filter fun θ => liesAbove hSigma ξ θ).card) * ξ 1 :=
          congrArg (· * ξ 1) hdeg'
      _ = _ := by ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ θ ∈ Pf, (∑ ξ ∈ famFin, if liesAbove hSigma ξ θ then ξ 1 else 0) =
      (Nat.card Sigma : ℂ) * D := by
    intro θ hθ
    rw [← Finset.sum_filter, hfamFin, sum_degree_above_twist hSigma ↑Pf hθ (hirr θ hθ),
      hdegPf θ hθ]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  ring

theorem exists_degree_of_mem_aboveFamily {Pf : Set (CentralExtension F b m hm heven → ℂ)}
    (hirr : ∀ θ ∈ Pf, θ ∈ BlocksIrr (CentralExtension F b m hm heven))
    {ξ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ} (hξ : ξ ∈ aboveFamily hSigma Pf) :
    ∃ θ ∈ Pf, ξ 1 = ((twistStabilizer hSigma θ).index : ℂ) * θ 1 := by
  obtain ⟨hξirr, θ, hθ, habove⟩ := hξ
  obtain ⟨χ, hχ, hres⟩ := exists_inertia_extension (hm := hm) (heven := heven) hSigma (hirr θ hθ)
  obtain ⟨hdeg, -, hiff, -, -⟩ := twist_clifford hSigma (hirr θ hθ) hχ hres
  obtain ⟨ρ, rfl⟩ := (hiff ξ hξirr).mp habove
  exact ⟨θ, hθ, (hdeg ρ).2⟩

theorem exists_fieldTwist_of_liesAbove {θ θ' : CentralExtension F b m hm heven → ℂ}
    (hθ : θ ∈ BlocksIrr (CentralExtension F b m hm heven))
    (hθ' : θ' ∈ BlocksIrr (CentralExtension F b m hm heven))
    {ξ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ}
    (hξ : ξ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma))
    (h1 : liesAbove hSigma ξ θ) (h2 : liesAbove hSigma ξ θ') :
    ∃ σ : Sigma, θ' = fieldTwist hSigma σ θ := by
  obtain ⟨χ, hχ, hres⟩ := exists_inertia_extension (hm := hm) (heven := heven) hSigma hθ
  obtain ⟨-, -, hiff, hrest, -⟩ := twist_clifford hSigma hθ hχ hres
  obtain ⟨ρ, rfl⟩ := (hiff ξ hξ).mp h1
  obtain ⟨C, hC⟩ := CFSG.Wreathed.exists_leftCoset_reps (twistStabilizer hSigma θ)
  obtain ⟨hsum, -, -⟩ := hrest C hC
  by_contra hnot
  unfold liesAbove at h2
  rw [hsum ρ, CFSG.Wreathed.blocksInnerProduct_finset_sum_left] at h2
  rw [Finset.sum_eq_zero fun σ _ => by
    have h3 := blocksInnerProduct_irreducible ⟨_, fieldTwist_mem_blocksIrr hSigma hθ σ⟩ ⟨_, hθ'⟩
    change BlocksInnerProduct (fieldTwist hSigma σ θ) θ' = _ at h3
    rw [h3, ite_eq_right]
    intro heq
    exact hnot ⟨σ, (congrArg Subtype.val heq).symm⟩] at h2
  exact lt_irrefl 0 h2

theorem not_liesAbove_of_degree_ne {Pf : Set (CentralExtension F b m hm heven → ℂ)} {D : ℂ}
    (hirr : ∀ θ ∈ Pf, θ ∈ BlocksIrr (CentralExtension F b m hm heven))
    (hdegPf : ∀ θ ∈ Pf, θ 1 = D)
    {ξ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ} (hξ : ξ ∈ aboveFamily hSigma Pf)
    {θ' : CentralExtension F b m hm heven → ℂ}
    (hθ' : θ' ∈ BlocksIrr (CentralExtension F b m hm heven)) (hne : θ' 1 ≠ D) :
    ¬ liesAbove hSigma ξ θ' := by
  obtain ⟨hξirr, θ, hθ, habove⟩ := hξ
  intro habove'
  obtain ⟨σ, rfl⟩ := exists_fieldTwist_of_liesAbove hSigma (hirr θ hθ) hθ' hξirr habove habove'
  exact hne (by rw [fieldTwist_apply_one, hdegPf θ hθ])


end Above

end CFSG.Wreathed.CentralSL2
