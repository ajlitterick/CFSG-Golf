module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOne
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
public import CFSG.LieType.Steinberg.CentralExt.UnitaryLift
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeLift

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial

section Split

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

local notation "σ₀" => unitaryInvolution F p f

theorem exists_rankOne_section_SU (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) {E : Type*} [Group E] [Finite E] {π : E →* SU σ₀ n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (k : Fin (n / 2)) :
    ∃ φ : ↥(CFSG.LieType.CurtisTits.rankOne
      (rootGroup σ₀ (unitaryInvolution_involutive hF) n) k) →* E, ∀ g, π (φ g) = g := by
  have hF2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact hp2
  by_cases hk : k.val + 1 < n / 2
  · exact exists_rankOne_short_section hk hF2 hπ hcen h2
  by_cases he : Even n
  · obtain ⟨e⟩ := nonempty_rankOne_last_even_mulEquiv hF he hn hk
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
    set e' := e.trans (hypEquiv hζ0 hζ).symm
    have hk2 : ringChar (fixedSubfield F p f) ≠ 2 := by
      rw [ringChar_fixedSubfield]
      exact hp2
    obtain ⟨ρ, hρ⟩ := CFSG.LieType.CentralExt.exists_lift hk2 hπ hcen h2
      ((Subgroup.subtype _).comp e'.symm.toMonoidHom)
    refine ⟨ρ.comp e'.toMonoidHom, fun g => ?_⟩
    have h := DFunLike.congr_fun hρ (e' g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h
    exact h
  · obtain ⟨e⟩ := nonempty_rankOne_last_odd_mulEquiv hF he (by
      obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.1 he
      omega) hk
    obtain ⟨ρ, hρ⟩ := exists_lift_SU_three hF hp2 hπ hcen h2
      ((Subgroup.subtype _).comp e.symm.toMonoidHom)
    refine ⟨ρ.comp e.toMonoidHom, fun g => ?_⟩
    have h := DFunLike.congr_fun hρ (e g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h
    exact h

theorem su_central_two_extension_splitting (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 2 ≤ n) {E : Type*} [Group E] [Finite E] {π : E →* SU σ₀ n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ s : SU σ₀ n →* E, (∀ x, π (s x) = x) ∧ (∀ τ : SU σ₀ n →* E, (∀ x, π (τ x) = x) → τ = s) ∧
      ∃ e : π.ker × s.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hC : ¬ p ∣ Nat.card π.ker :=
    CFSG.LieType.CentralExt.not_dvd_card_of_isPGroup_two h2 Fact.out hp2
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact exists_section_mulEquiv_of_existsUnique hcen (existsUnique_section_of_rankOne_lift
    (D := rootDatum hF n) (isCTGroupDatum hF n hn ζ hζ) (steinbergExtras hF n hn ζ hζ)
    (fun γ hγ => isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (SUExtras.toStd_ne_zero_of_mem_roots hγ)) hπ hcen hC
    (exists_rankOne_section_SU hF hp2 hn hπ hcen h2))

end Split


end CFSG.LieType.Steinberg
