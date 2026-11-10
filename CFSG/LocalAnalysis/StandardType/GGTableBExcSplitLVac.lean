module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMore
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreExc
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerBstar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CorFourTwoOpen

namespace ExcSplitL


theorem mem_chevID_E6_of_pow {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpf : ¬ p ∣ f)
    (φ : MulAut (LargeEvenCenterQuot (LargeEvenChevH TwistTag.E6.tag.cartan K false)))
    (hφ : φ ^ p = 1) :
    φ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K
      (LargeEvenChevH TwistTag.E6.tag.cartan K false) := by
  have hQ := (RecipeFieldE6.e6QuotOn_isRoot K).of_eq
    (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  unfold RecipeFieldE6.E6QuotOn at hQ
  rw [← InndiagE6.diagHom_eq_markDiagUnit] at hQ
  have hcard : Nat.card (K ≃+* K) = f := by
    obtain ⟨-, -, -, -, hc, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two hf hK
    exact hc
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hcop : Nat.Coprime p (2 * f) := Nat.Coprime.mul_right
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpf)
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.chevH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K false →
      ∀ ψ : MulAut (LargeEvenCenterQuot H), ψ ^ p = 1 →
        ψ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K H from
    key _ (largeEvenChevH_eq _ K false) φ hφ
  intro H hH
  subst hH
  obtain ⟨Ψ, hker, -⟩ := hQ
  intro ψ hψ
  have h1 : Ψ ψ ^ p = 1 := by rw [← map_pow, hψ, map_one]
  have hall : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
  have h2 : Ψ ψ ^ (2 * f) = 1 := by
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst, Prod.fst_one, pow_mul', ← hcard, pow_card_eq_one', one_pow]
    · rw [Prod.pow_snd, Prod.snd_one, pow_mul]
      have h3 : (Ψ ψ).2 ^ 2 = 1 := hall _
      rw [h3, one_pow]
  have h3 : orderOf (Ψ ψ) = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  exact RecipeFieldE6.mem_chevID_iff_isInnDiagOn.mpr ((hker ψ).mp (orderOf_eq_one_iff.mp h3))

end ExcSplitL

open ExcSplitL

@[expose] def GGExcLVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ≠ 2 ∧ (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6) ∧
    ¬ p ∣ lab.n


section Labels


theorem largeEvenLabelAll_pow_mem_excLVac {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGExcLVacLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hp2, htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag hpn hn
  rcases htag with rfl | rfl | rfl | rfl | rfl
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeChevalley_and (fun K _ _ hK => mem_chevID_E6_of_pow hn K hK hp hp2 hpn) hQ
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeChevalley_and (fun K _ _ hK φ hφ => Subgroup.subset_closure
      (Or.inl (IOneRest.mem_range_conj_recipe_of_pow (τ := .E7) (Or.inl rfl) hn hK hp hpn hφ)))
      hQ
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeChevalley_and (fun K _ _ hK φ hφ => Subgroup.subset_closure
      (Or.inl (IOneRest.mem_range_conj_recipe_of_pow (τ := .E8) (Or.inr rfl) hn hK hp hpn hφ)))
      hQ
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine recipeChevalley_and (fun K _ _ hK φ hφ => ?_) hQ
    have : CharP K 2 := charP_two_of_card hK
    exact Subgroup.subset_closure
      (Or.inl (IOneRest.mem_range_conj_recipeF4_of_pow hn hK hp hp2 hpn hφ))
  · exact TwE6Delta.labelAll (lab := ⟨.twE6, l, n⟩) rfl fun K _ _ hK φ hφ =>
      TwE6Per.mem_recipeI_of_pow_eq_one hn hK hp hp2 hpn hφ

theorem ggBstarInnerDiagLInputOn_excLVac (T : ℕ → LargeEvenLabel → Prop) :
    GGBstarInnerDiagLInputOn fun p lab => T p lab ∧ GGExcLVacLabel p lab :=
  ggBstarInnerDiagLInputOn_of_pow ggLNoncyclicInput_holds fun _ _ hp hlab h =>
    largeEvenLabelAll_pow_mem_excLVac hp hlab h.2


end Labels

end CFSG.StandardType

end
