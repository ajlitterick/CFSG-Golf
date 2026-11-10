module

public import CFSG.RankThree.PartOne.S11d.PlaneAll
public import CFSG.RankThree.PartOne.S11c.Sec68

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.Blueprint (Catalog)
open CFSG.Assembly.RankThreeEven (localRank)

section Rank

variable {G : Type} [Group G] [Finite G] {I : Subgroup G} {Γ : Type} [Group Γ] [Finite Γ]
  {K : Subgroup Γ}

omit [Finite G] [Finite Γ] in
theorem surjective_centerQuotient_comp (π₀ : ↥I →* ↥K) (hπ₀ : Function.Surjective π₀) :
    Function.Surjective ((QuotientGroup.mk' (Subgroup.center ↥K)).comp π₀) :=
  (QuotientGroup.mk'_surjective _).comp hπ₀

theorem sec68_psl_section (he : evenRank G ≤ 3) (π₀ : ↥I →* ↥K) (hπ₀ : Function.Surjective π₀)
    {p ℓ n f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hloc : localRank p Γ ≤ 3)
    (hmod : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f - 1) : False := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hmod0 := hmod
  obtain ⟨⟨hℓ, hf, hn2, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime' hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have := Fintype.ofFinite k
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hchar : CharP k ℓ := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hk])
  have hpk : p ∣ Fintype.card k - 1 := by rwa [← Nat.card_eq_fintype_card, hk]
  let ψ : ↥K ⧸ Subgroup.center ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm
  let φ₂ : ↥K →* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφs : Function.Surjective φ₂ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨-, -, -, -, -, -, -, hle⟩ :=
    CFSG.RankThree.CentralCover.linear_split_prime_central_cover_two_local_rank K hℓ hp hp3 hpk
      (by omega) φ₂ hφs (quotient_cover_ker ψ)
  have hn : n = 5 := by
    by_cases hℓ2 : ℓ = 2
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      by_contra hne
      have h6 : n = 6 := by omega
      exact not_dvd_six hp hp3 (h6 ▸ hpn)
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      omega
  subst hn
  have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpn
  subst hp5'
  have hπ := surjective_centerQuotient_comp π₀ hπ₀
  have h4 : 4 ≤ evenRank G := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact (even_square_field_linear_five_sections_force_two_local_rank_four (G := G)).1 hf
        (even_of_five_dvd_two_pow_sub_one hpq) hmod0 I _ hπ
    · exact (odd_characteristic_split_degree_five_sections_force_two_local_rank_four
        (G := G)).1 hℓ hℓ2 hf (Or.inl rfl) (Or.inl ⟨rfl, hpq⟩) hmod0 I _ hπ
  omega

theorem sec68_psu_section (he : evenRank G ≤ 3) (π₀ : ↥I →* ↥K) (hπ₀ : Function.Surjective π₀)
    {p ℓ n f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hloc : localRank p Γ ≤ 3)
    (hmod : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSU n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f + 1) : ℓ = 2 ∧ n = 5 ∧ p = 5 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hmod0 := hmod
  obtain ⟨⟨hℓ, hf, hn3, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime' hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f k :=
    ⟨hℓ, hf, by rw [hk, ← pow_mul, mul_comm]⟩
  let ψ : ↥K ⧸ Subgroup.center ↥K ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm
  let φ₂ : ↥K →* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφs : Function.Surjective φ₂ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨u, -, hu, V, hV, hVab, hVcard⟩ :=
    CFSG.RankThree.Classical2.unitary_split_prime_central_cover_two_local_rank K hU hp hp3 hpq
      (by omega) φ₂ hφs (quotient_cover_ker ψ)
  have hle := CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian hp hu
    (le_inf_iff.mp hV).2 hVab hVcard
  have hn : n = 5 := by
    by_cases hℓ2 : ℓ = 2
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      by_contra hne
      have h6 : n = 6 := by omega
      exact not_dvd_six hp hp3 (h6 ▸ hpn)
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      omega
  subst hn
  have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpn
  subst hp5'
  by_cases hℓ2 : ℓ = 2
  · exact ⟨hℓ2, rfl, rfl⟩
  · exfalso
    have hπ := surjective_centerQuotient_comp π₀ hπ₀
    have h4 : 4 ≤ evenRank G :=
      (odd_characteristic_split_degree_five_sections_force_two_local_rank_four
        (G := G)).1 hℓ hℓ2 hf (Or.inr rfl) (Or.inr ⟨rfl, hpq⟩) hmod0 I _ hπ
    omega

end Rank

section Main


end Main

end CFSG.RankThree.PartOne
