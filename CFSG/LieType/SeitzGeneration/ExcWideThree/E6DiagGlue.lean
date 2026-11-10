module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTwisted
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.LangStep
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Pair
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Rigid
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.TwLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagAssembly
public import CFSG.Sporadic.Suz.Simple

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE

section FR


end FR

end CFSG.LieType.SeitzGeneration.ExcHighThree

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


theorem exists_outer_matrix (K : Type) [Field K] [Finite K]
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : E ≤ e6Inndiag K)
    (hnin : ¬ E ≤ innerAut (adjointGroup Tag.E6 K)) :
    ∃ x ∈ e6PlanePre K E, x ∉ adjointGroup Tag.E6 K := by
  by_contra h
  push Not at h
  apply hnin
  intro ε hε
  have hεr : ε ∈ (e6InndiagConj K).range := by
    rw [range_e6InndiagConj]
    exact hE hε
  obtain ⟨g, rfl⟩ := hεr
  have hg : (g : ModGL Tag.E6 K) ∈ e6PlanePre K E := (mem_e6PlanePre_iff K E _).2 ⟨g, rfl, hε⟩
  refine ⟨⟨g, h _ hg⟩, ?_⟩
  ext y
  rfl

theorem exists_langGLData (htor : E6PlaneToralLang) {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁]
    (hroot : ∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c)
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hd : E ≤ e6Inndiag K)
    (hiso : E6DiagIsotropic K K₁ E) :
    Nonempty (LangGLData Tag.E6 K (e6PlanePre K E)) := by
  have h3 : ¬ 3 ∣ Nat.card K := not_three_dvd_card_of_ringChar K hK3
  have hinj := e6InndiagConj_injective K hK4
  have hEr : E ≤ (e6InndiagConj K).range := by
    rw [range_e6InndiagConj]; exact hd
  have hmap : (E.comap (e6InndiagConj K)).map (e6InndiagConj K) = E :=
    Subgroup.map_comap_eq_self hEr
  have hexp : ∀ x ∈ E.comap (e6InndiagConj K), x ^ 3 = 1 := fun x hx =>
    hinj (by rw [map_pow, map_one]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hx)
  have hcard₀ : Nat.card (E.comap (e6InndiagConj K)) = 3 ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]; exact hcard
  have hC₁ : ∀ x ∈ E.comap (e6InndiagConj K), baseChangeGL (algebraMap K K₁)
      (x : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 K₁ := fun x _ =>
    map_e6InndiagGL_le _ hroot (Subgroup.mem_map_of_mem _ x.2)
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hin⟩ :=
    e6IsotropicToralInndiag_of_planeToralLang htor K h3 K₁ (E.comap (e6InndiagConj K)) hexp hcard₀
      hC₁ (fun x y hx hy => hiso x y hx hy)
  refine ⟨⟨w, Fr, hFr, g0, hg0C, hg0, 1, one_mem _, fun x hx => ?_⟩⟩
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hin y hy

@[expose] def E6HeisenbergParabolic : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁],
      (∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c) →
      ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), CFSG.IsElementaryAbelian 3 E →
        Nat.card E = 3 ^ 2 → E ≤ e6Inndiag K → ¬ E ≤ innerAut (adjointGroup Tag.E6 K) →
        ¬ E6DiagIsotropic K K₁ E → E6NormalizesR K E

theorem e6InndiagTorality_of_heisenberg (hH : E6HeisenbergParabolic) : E6InndiagTorality := by
  intro K _ _ hK3 E hE hEab hcard hnin
  obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
  have hK4 := four_le_card_of_not_innerAut K hK3 E hE hnin
  by_cases hiso : E6DiagIsotropic K K₁ E
  · left
    obtain ⟨D⟩ := exists_langGLData e6PlaneToralLang_proved hK3 hK4 K₁ hroot E hEab hcard hE hiso
    exact ⟨D, exists_outer_matrix K E hE hnin⟩
  · right
    exact hH K hK3 K₁ hroot E hEab hcard hE hnin hiso


theorem matrix_of_e6NormalizesR {K : Type} [Field K] [Finite K]
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : E ≤ e6Inndiag K)
    (h : E6NormalizesR K E) :
    ∃ R : Subgroup (ModGL Tag.E6 K), R ≤ adjointGroup Tag.E6 K ∧ R ≠ ⊥ ∧
      IsPGroup (ringChar K) R ∧ e6PlanePre K E ≤ Subgroup.normalizer (R : Set (ModGL Tag.E6 K)) := by
  obtain ⟨R, hR1, hRp, hRn⟩ := h
  refine ⟨R.map (adjointGroup Tag.E6 K).subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, -, rfl⟩
    exact r.2
  · intro hbot
    apply hR1
    exact (Subgroup.map_eq_bot_iff_of_injective R (adjointGroup Tag.E6 K).subtype_injective).1 hbot
  · exact hRp.map _
  · intro x hx
    obtain ⟨g, rfl, hgE⟩ := (mem_e6PlanePre_iff K E x).1 hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : e6InndiagConj K g r ∈ R.map (e6InndiagConj K g).toMonoidHom := ⟨r, hr, rfl⟩
      rw [hRn _ hgE] at hr'
      exact ⟨_, hr', by simp [e6InndiagConj_apply]⟩
    · rintro ⟨r', hr', hy⟩
      have hr'' : r' ∈ R.map (e6InndiagConj K g).toMonoidHom := by rw [hRn _ hgE]; exact hr'
      obtain ⟨r, hr, rfl⟩ := hr''
      refine ⟨r, hr, ?_⟩
      have h1 : (g : ModGL Tag.E6 K) * (r : ModGL Tag.E6 K) * (g : ModGL Tag.E6 K)⁻¹ =
          (g : ModGL Tag.E6 K) * y * (g : ModGL Tag.E6 K)⁻¹ := by
        rw [← e6InndiagConj_apply]
        exact hy
      have := mul_left_cancel (mul_right_cancel h1)
      exact this


end CFSG.LieType.SeitzGeneration.ExcWideThree

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


@[expose] def TwE6InndiagTorality' : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (twistedE6RootGroup K σ) →
      (∃ D : TwLangData K σ q (twPlanePre K σ E), ∃ x ∈ twPlanePre K σ E,
          x ∉ twistedE6RootGroup K σ) ∨ TwE6NormalizesR K σ E

@[expose] def TwE6InndiagParabolic' : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (twistedE6RootGroup K σ) → TwE6NormalizesR K σ E →
      Subgroup.closure (fixUnion E) = ⊤


theorem exists_outer_matrix_tw (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (hE : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hnin : ¬ E ≤ innerAut (twistedE6RootGroup K σ)) :
    ∃ x ∈ twPlanePre K σ E, x ∉ twistedE6RootGroup K σ := by
  by_contra h
  push Not at h
  apply hnin
  intro ε hε
  have hεr : ε ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact hE hε
  obtain ⟨g, rfl⟩ := hεr
  have hg : (g : ModGL TwistTag.E6.tag K) ∈ twPlanePre K σ E :=
    (mem_twPlanePre_iff K σ E _).2 ⟨g, rfl, hε⟩
  refine ⟨⟨g, h _ hg⟩, ?_⟩
  ext y
  rfl

theorem exists_twLangData (htor : TwistedE6PlaneToralLang) (ℓ f : ℕ) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁]
    (hroot : ∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hd : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hiso : TwistedE6DiagIsotropic K σ K₁ E) :
    Nonempty (TwLangData K σ (ℓ ^ f) (twPlanePre K σ E)) := by
  have hinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hEr : E ≤ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]; exact hd
  have hmap : (E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagConj K σ) = E :=
    Subgroup.map_comap_eq_self hEr
  have hexp : ∀ x ∈ E.comap (twistedE6InndiagConj K σ), x ^ 3 = 1 := fun x hx =>
    hinj (by rw [map_pow, map_one]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hx)
  have hcard₀ : Nat.card (E.comap (twistedE6InndiagConj K σ)) = 3 ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]; exact hcard
  have hC₁ : ∀ x ∈ E.comap (twistedE6InndiagConj K σ), baseChangeGL (algebraMap K K₁)
      (x : ModGL TwistTag.E6.tag K) ∈ adjointGroup Tag.E6 K₁ := fun x _ =>
    map_twistedE6InndiagGL_le σ _ hroot (Subgroup.mem_map_of_mem _ x.2)
  obtain ⟨v, Fr, hFr, g0, hg0C, hg0, hin⟩ :=
    twistedE6IsotropicToralInndiag_of_planeToralLang htor ℓ f hℓ hℓ3 hf K hK σ hσ K₁
      (E.comap (twistedE6InndiagConj K σ)) hexp hcard₀ hC₁ (fun x y hx hy => hiso x y hx hy)
  refine ⟨⟨v, Fr, hFr, g0, hg0C, hg0, 1, one_mem _, fun x hx => ?_⟩⟩
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hin y hy

@[expose] def TwE6HeisenbergParabolic : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁],
      (∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c) →
      ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
        E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E →
        Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (twistedE6RootGroup K σ) →
        ¬ TwistedE6DiagIsotropic K σ K₁ E → TwE6NormalizesR K σ E

theorem twE6InndiagTorality'_of_heisenberg (hH : TwE6HeisenbergParabolic) :
    TwE6InndiagTorality' := by
  intro K _ _ σ q hK3 hσ hK E hE hEab hcard hnin
  obtain ⟨hp, f, hf, rfl⟩ := ExcHighThree.exists_pow_ringChar_of_card_sq K q hK
    (by
      by_contra h
      have hq : q ≤ 1 := by omega
      have : Nat.card K ≤ 1 := by
        rw [hK]; nlinarith [Nat.zero_le q]
      have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
      omega)
  obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
  by_cases hiso : TwistedE6DiagIsotropic K σ K₁ E
  · left
    obtain ⟨D⟩ := exists_twLangData twistedE6PlaneToralLang_proved (ringChar K) f hp hK3 hf hK σ hσ
      K₁ hroot E hEab hcard hE hiso
    exact ⟨D, exists_outer_matrix_tw K σ E hE hnin⟩
  · right
    exact hH K σ _ hK3 hσ hK K₁ hroot E hE hEab hcard hnin hiso

end CFSG.LieType.SeitzGeneration.ExcWideThree

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny


@[expose] def TwE6InndiagCentralizerGeneration : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ (A : Subgroup (ModGL TwistTag.E6.tag K)), A ≤ twistedE6InndiagGL K σ →
      CFSG.IsElementaryAbelian 3 A → 3 ^ 2 ≤ Nat.card A →
      ∀ R : Subgroup (ModGL TwistTag.E6.tag K), R ≤ twistedE6RootGroup K σ →
        IsPGroup (ringChar K) R → R ≠ ⊥ →
        A ≤ Subgroup.normalizer (R : Set (ModGL TwistTag.E6.tag K)) →
        (⨆ a ∈ A, ⨆ (_ : a ≠ 1), twistedE6RootGroup K σ ⊓
          Subgroup.centralizer ({a} : Set (ModGL TwistTag.E6.tag K))) = twistedE6RootGroup K σ

theorem matrix_of_twE6NormalizesR {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ)))
    (hE : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (h : TwE6NormalizesR K σ E) :
    ∃ R : Subgroup (ModGL TwistTag.E6.tag K), R ≤ twistedE6RootGroup K σ ∧ R ≠ ⊥ ∧
      IsPGroup (ringChar K) R ∧
      twPlanePre K σ E ≤ Subgroup.normalizer (R : Set (ModGL TwistTag.E6.tag K)) := by
  obtain ⟨R, hR1, hRp, hRn⟩ := h
  refine ⟨R.map (twistedE6RootGroup K σ).subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, -, rfl⟩
    exact r.2
  · intro hbot
    apply hR1
    exact (Subgroup.map_eq_bot_iff_of_injective R (twistedE6RootGroup K σ).subtype_injective).1 hbot
  · exact hRp.map _
  · intro x hx
    obtain ⟨g, rfl, hgE⟩ := (mem_twPlanePre_iff K σ E x).1 hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : twistedE6InndiagConj K σ g r ∈ R.map (twistedE6InndiagConj K σ g).toMonoidHom :=
        ⟨r, hr, rfl⟩
      rw [hRn _ hgE] at hr'
      exact ⟨_, hr', by simp [twistedE6InndiagConj_apply]⟩
    · rintro ⟨r', hr', hy⟩
      have hr'' : r' ∈ R.map (twistedE6InndiagConj K σ g).toMonoidHom := by
        rw [hRn _ hgE]; exact hr'
      obtain ⟨r, hr, rfl⟩ := hr''
      refine ⟨r, hr, ?_⟩
      have h1 : (g : ModGL TwistTag.E6.tag K) * (r : ModGL TwistTag.E6.tag K) *
          (g : ModGL TwistTag.E6.tag K)⁻¹ =
          (g : ModGL TwistTag.E6.tag K) * y * (g : ModGL TwistTag.E6.tag K)⁻¹ := by
        rw [← twistedE6InndiagConj_apply]
        exact hy
      exact mul_left_cancel (mul_right_cancel h1)

theorem twE6InndiagParabolic'_of_generic (hG : TwE6InndiagCentralizerGeneration) :
    TwE6InndiagParabolic' := by
  intro K _ _ σ q hK3 hσ hK E hE hEab hcard hnin hnorm
  classical
  obtain ⟨hp, f, hf, rfl⟩ := ExcHighThree.exists_pow_ringChar_of_card_sq K q hK
    (by
      by_contra h
      have hq : q ≤ 1 := by omega
      have : Nat.card K ≤ 1 := by
        rw [hK]; nlinarith [Nat.zero_le q]
      have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
      omega)
  have hinj := twistedE6InndiagConj_injective hp hf hK σ hσ
  obtain ⟨R, hRC, hR1, hRp, hRn⟩ := matrix_of_twE6NormalizesR σ E hE hnorm
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hAle : twPlanePre K σ E ≤ twistedE6InndiagGL K σ := by
    rintro _ hx
    obtain ⟨g, rfl, -⟩ := (mem_twPlanePre_iff K σ E _).1 hx
    exact g.2
  have hAcomm : ∀ a ∈ twPlanePre K σ E, ∀ b ∈ twPlanePre K σ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, rfl, hg⟩ := (mem_twPlanePre_iff K σ E a).1 ha
    obtain ⟨h, rfl, hh⟩ := (mem_twPlanePre_iff K σ E b).1 hb
    have : g * h = h * g := by
      apply hinj
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hEab.is_comm.comm ⟨_, hg⟩ ⟨_, hh⟩)
    exact congrArg Subtype.val this
  have hAEA : CFSG.IsElementaryAbelian 3 (twPlanePre K σ E) :=
    CFSG.IsElementaryAbelian.of_forall hAcomm fun a ha =>
      pow_three_eq_one_of_mem_twPlanePre _ f hp hf K hK σ hσ E ha
  have hAcard : Nat.card (twPlanePre K σ E) = 3 ^ 2 := by
    rw [card_twPlanePre _ f hp hf K hK σ hσ E hE]
    exact hcard
  have hgen := hG K σ (ringChar K ^ f) hK3 hσ hK (twPlanePre K σ E) hAle hAEA hAcard.ge R hRC hRp
    hR1 hRn
  have hsub : ∀ a ∈ twPlanePre K σ E, a ≠ 1 →
      twistedE6RootGroup K σ ⊓ Subgroup.centralizer ({a} : Set (ModGL TwistTag.E6.tag K)) ≤
      (Subgroup.closure (fixUnion E)).map (twistedE6RootGroup K σ).subtype := by
    intro a ha ha1 y hy
    obtain ⟨g, rfl, hgE⟩ := (mem_twPlanePre_iff K σ E a).1 ha
    have hyC : y ∈ twistedE6RootGroup K σ := hy.1
    have hcomm : (g : ModGL TwistTag.E6.tag K) * y = y * (g : ModGL TwistTag.E6.tag K) :=
      Subgroup.mem_centralizer_iff.1 hy.2 (g : ModGL TwistTag.E6.tag K) rfl
    refine ⟨⟨y, hyC⟩, Subgroup.subset_closure ?_, rfl⟩
    refine ⟨Subgroup.zpowers (twistedE6InndiagConj K σ g), ?_, ?_, ?_⟩
    · rw [Subgroup.zpowers_le]
      exact hgE
    · intro hbot
      have hmem : twistedE6InndiagConj K σ g ∈ (⊥ : Subgroup (MulAut ↥(twistedE6RootGroup K σ))) :=
        hbot ▸ Subgroup.mem_zpowers _
      have : g = 1 := hinj (by simpa using hmem)
      exact ha1 (by rw [this]; rfl)
    · intro φ hφ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
      rw [← map_zpow]
      apply Subtype.ext
      rw [twistedE6InndiagConj_apply]
      have hc : Commute (y : ModGL TwistTag.E6.tag K)
          ((g ^ n : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K) := by
        have h1 : Commute (y : ModGL TwistTag.E6.tag K) (g : ModGL TwistTag.E6.tag K) := hcomm.symm
        simpa using h1.zpow_right n
      calc ((g ^ n : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K) * y *
            ((g ^ n : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K)⁻¹
          = y * ((g ^ n : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K) *
              ((g ^ n : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K)⁻¹ := by rw [hc.eq]
        _ = y := by group
  have hle : twistedE6RootGroup K σ ≤
      (Subgroup.closure (fixUnion E)).map (twistedE6RootGroup K σ).subtype := by
    exact le_trans (le_of_eq hgen.symm) (iSup₂_le fun a ha => iSup_le fun ha1 => hsub a ha ha1)
  rw [eq_top_iff]
  intro y _
  obtain ⟨t, ht, hty⟩ := hle y.2
  have : t = y := Subtype.ext hty
  rw [← this]
  exact ht


end CFSG.LieType.SeitzGeneration.ExcWideThree

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross


structure E6HeisenbergFrame (K : Type) [Field K] [Finite K]
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) where
  w' : WeylGroup Tag.E6
  Fr : AlgebraicClosure K →+* AlgebraicClosure K
  hFr : ∀ c, Fr c = c ^ Nat.card K
  g0 : ModGL Tag.E6 (AlgebraicClosure K)
  hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K)
  hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w'
  a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ
  b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ
  w : WeylGroup Tag.E6
  ha3 : ∀ i, a i ^ 3 = 1
  hw : w ∈ rootCharStabilizer a
  hsh : rootChar a (e6Shift w) ≠ 1
  hT : rootDiagUnit Tag.E6 a ∈ twistedTorusOf
    (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w') (Units.map (entrywiseHom Fr))
  u : ModGL Tag.E6 (AlgebraicClosure K)
  hu : u ∈ rootSpan Tag.E6 (AlgebraicClosure K) (rootCharKernel a)
  g₁ : ↥(e6InndiagGL K)
  g₂ : ↥(e6InndiagGL K)
  hg₁ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g₁ : ModGL Tag.E6 K) * g0 =
    rootDiagUnit Tag.E6 a
  hg₂ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g₂ : ModGL Tag.E6 K) * g0 =
    u⁻¹ * (rootDiagUnit Tag.E6 b *
      canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w) * u
  hE₁ : e6InndiagConj K g₁ ∈ E
  hE₂ : e6InndiagConj K g₂ ∈ E
  hgen : E = Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂}

theorem exists_e6HeisenbergFrame {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁]
    (hroot : ∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c)
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hd : E ≤ e6Inndiag K) (hnoniso : ¬ E6DiagIsotropic K K₁ E) :
    Nonempty (E6HeisenbergFrame K E) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h3 : ¬ 3 ∣ Nat.card K := not_three_dvd_card_of_ringChar K hK3
  have hinj := e6InndiagConj_injective K hK4
  have hnoniso' : ∃ s t : ↥(e6Data_valid.minGroup K₁),
      (e6Isogeny K₁ s : ModGL Tag.E6 K₁) ∈
        ((E.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧
      (e6Isogeny K₁ t : ModGL Tag.E6 K₁) ∈
        ((E.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧ s * t ≠ t * s := by
    unfold E6DiagIsotropic at hnoniso
    push Not at hnoniso
    exact hnoniso
  obtain ⟨s, t, hs, ht, hst⟩ := hnoniso'
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, hs1⟩ := hs
  obtain ⟨_, ⟨g₂, hg₂, rfl⟩, ht1⟩ := ht
  have hg₁3 : g₁ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) _ hg₁)
  have hg₂3 : g₂ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) _ hg₂)
  have hcomm₀ : g₁ * g₂ = g₂ * g₁ := by
    refine hinj ?_
    have := congrArg Subtype.val
      (hE.is_comm.comm ⟨e6InndiagConj K g₁, hg₁⟩ ⟨e6InndiagConj K g₂, hg₂⟩)
    rw [map_mul, map_mul]
    exact this
  have hd₁3 : (g₁ : ModGL Tag.E6 K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₁3
  have hd₂3 : (g₂ : ModGL Tag.E6 K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₂3
  have hcomm : (g₁ : ModGL Tag.E6 K) * g₂ = g₂ * g₁ := by
    simpa using congrArg Subtype.val hcomm₀
  obtain ⟨c₂, hc₂, a, b, w, ha3, hw, hsh, hca, hcb⟩ :=
    E6Heis.pair_normal_form h3 K₁ (g₁ : ModGL Tag.E6 K) (g₂ : ModGL Tag.E6 K) g₁.2 g₂.2 hd₁3
      hd₂3 hcomm s t hs1.symm ht1.symm hst
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  set ι₀ : K →+* L := algebraMap K L with hι₀
  set Fr : L →+* L := iterateFrobenius L ℓ (f : ℕ) with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFrdef, iterateFrobenius_def, Nat.card_eq_fintype_card, hf]
  have hcomp : Fr.comp ι₀ = ι₀ := by
    refine RingHom.ext fun c => ?_
    change Fr (ι₀ c) = ι₀ c
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hFix : Units.map (entrywiseHom Fr) (baseChangeGL ι₀ (g₁ : ModGL Tag.E6 K)) =
      baseChangeGL ι₀ (g₁ : ModGL Tag.E6 K) := by
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hpq : Nat.Coprime 3 (ℓ ^ (f : ℕ)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (by rw [← hf, ← Nat.card_eq_fintype_card]; exact h3)
  have hga : (c₂⁻¹)⁻¹ * baseChangeGL ι₀ (g₁ : ModGL Tag.E6 K) * c₂⁻¹ = rootDiagUnit Tag.E6 a := by
    rw [inv_inv]
    exact hca
  obtain ⟨w', z, hz, hu, hga', hT⟩ := E6Heis.lang_step_single (L := L) (ℓ := ℓ) (f : ℕ) f.pos hpq
    (inv_mem hc₂) a ha3 hga hFix
  have hzC : z ∈ adjointGroup Tag.E6 L :=
    sup_le torusGroup_le_adjointGroup' (rootSpan_le_adjointGroup L _) hz
  have hg0C : c₂⁻¹ * z ∈ adjointGroup Tag.E6 L := mul_mem (inv_mem hc₂) hzC
  obtain ⟨u, b', hu', hconj⟩ := E6Heis.exists_rootSpan_conj_form a b w (m := z) hz
  have hg₂' : (c₂⁻¹ * z)⁻¹ * baseChangeGL ι₀ (g₂ : ModGL Tag.E6 K) * (c₂⁻¹ * z) =
      u⁻¹ * (rootDiagUnit Tag.E6 b' * canonicalRep (coxeterSystem Tag.E6) L w) * u := by
    rw [← hconj, ← hcb]
    group
  have hker : ∀ g g' : ↥(e6Data_valid.minGroup K₁),
      ((e6Isogeny K₁ g : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ g' : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) →
      g'⁻¹ * g ∈ Subgroup.center ↥(e6Data_valid.minGroup K₁) := by
    intro g g' hgg'
    rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
    rw [MonoidHom.mem_ker]
    change e6Isogeny K₁ (g'⁻¹ * g) = 1
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact Subtype.ext hgg'.symm
  have hnot : ∀ k : ℤ, g₂ ≠ g₁ ^ k := by
    intro k hk
    apply hst
    have hπ : ((e6Isogeny K₁ t : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ (s ^ k) : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) := by
      rw [← ht1, hk, map_zpow (e6Isogeny K₁) s k, Subgroup.coe_zpow, ← hs1]
      simp [map_zpow]
    have hz1 := hker t (s ^ k) hπ
    have hsz : Commute s ((s ^ k)⁻¹ * t) := Subgroup.mem_center_iff.1 hz1 s
    have hsk : Commute s (s ^ k) := (Commute.refl s).zpow_right k
    have hct : Commute s t := by
      have := hsk.mul_right hsz
      rwa [mul_inv_cancel_left] at this
    exact hct.eq
  have he₁1 : e6InndiagConj K g₁ ≠ 1 := by
    intro h
    have hg1 : g₁ = 1 := hinj (h.trans (map_one _).symm)
    have hπ : ((e6Isogeny K₁ s : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ (1 : ↥(e6Data_valid.minGroup K₁)) : adjointGroup Tag.E6 K₁) :
          ModGL Tag.E6 K₁) := by
      rw [← hs1, hg1]
      simp
    have hz1 := hker s 1 hπ
    have hs_c : s ∈ Subgroup.center ↥(e6Data_valid.minGroup K₁) := by simpa using hz1
    exact hst (Subgroup.mem_center_iff.1 hs_c t).symm
  have he₂n : e6InndiagConj K g₂ ∉ Subgroup.zpowers (e6InndiagConj K g₁) := by
    rintro ⟨k, hk⟩
    apply hnot k
    apply hinj
    rw [map_zpow]
    exact hk.symm
  have hgen : E = Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂} := by
    have hle : Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂} ≤ E := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hg₁
      · exact hg₂
    have hz₁ : Subgroup.zpowers (e6InndiagConj K g₁) ≤
        Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂} := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    have he₂c : e6InndiagConj K g₂ ∈ Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have he₁o : orderOf (e6InndiagConj K g₁) = 3 := by
      refine orderOf_eq_prime ?_ he₁1
      rw [← map_pow, hg₁3, map_one]
    have hc1 : Nat.card (Subgroup.zpowers (e6InndiagConj K g₁)) = 3 := by
      rw [Nat.card_zpowers, he₁o]
    have hdvd1 : 3 ∣ Nat.card (Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂}) := by
      rw [← hc1]
      exact Subgroup.card_dvd_of_le hz₁
    have hdvd2 : Nat.card (Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂}) ∣ 3 ^ 2 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle
    have hne : Subgroup.zpowers (e6InndiagConj K g₁) ≠
        Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂} := fun h =>
      he₂n (h ▸ he₂c)
    have hne3 : Nat.card (Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂}) ≠ 3 := by
      intro h3'
      apply hne
      exact Subgroup.eq_of_le_of_card_ge hz₁ (by rw [hc1, h3'])
    have h9 : Nat.card (Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂}) = 3 ^ 2 := by
      have := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd2
      obtain ⟨m, hm, hm'⟩ := this
      interval_cases m
      · rw [hm', pow_zero] at hdvd1
        omega
      · exact absurd (by rw [hm']; norm_num) hne3
      · exact hm'
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hcard])).symm
  exact ⟨⟨w', Fr, hFr, c₂⁻¹ * z, hg0C, hu, a, b', w, ha3, hw, hsh, hT, u, hu', g₁, g₂, hga', hg₂',
    hg₁, hg₂, hgen⟩⟩


structure TwE6HeisenbergFrame (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) where
  w' : WeylGroup TwistTag.E6.tag
  Fr : AlgebraicClosure K →+* AlgebraicClosure K
  hFr : ∀ c, Fr c = c ^ q
  g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)
  hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K)
  hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
    g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w'
  a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ
  b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ
  w : WeylGroup Tag.E6
  ha3 : ∀ i, a i ^ 3 = 1
  hw : w ∈ rootCharStabilizer a
  hsh : rootChar a (e6Shift w) ≠ 1
  hT : rootDiagUnit TwistTag.E6.tag a ∈ twistedTorusOf
    (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w')
    (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)
  u : ModGL Tag.E6 (AlgebraicClosure K)
  hu : u ∈ rootSpan Tag.E6 (AlgebraicClosure K) (rootCharKernel a)
  g₁ : ↥(twistedE6InndiagGL K σ)
  g₂ : ↥(twistedE6InndiagGL K σ)
  hg₁ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g₁ : ModGL TwistTag.E6.tag K) * g0 =
    rootDiagUnit TwistTag.E6.tag a
  hg₂ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g₂ : ModGL TwistTag.E6.tag K) * g0 =
    u⁻¹ * (rootDiagUnit Tag.E6 b *
      canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w) * u
  hE₁ : twistedE6InndiagConj K σ g₁ ∈ E
  hE₂ : twistedE6InndiagConj K σ g₂ ∈ E
  hgen : E = Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂}

theorem exists_twE6HeisenbergFrame (ℓ f : ℕ) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁]
    (hroot : ∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hd : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hnoniso : ¬ TwistedE6DiagIsotropic K σ K₁ E) :
    Nonempty (TwE6HeisenbergFrame K σ (ℓ ^ f) E) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have h3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact h3 (Nat.prime_three.dvd_of_dvd_pow h)
  have hinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hnoniso' : ∃ s t : ↥(e6Data_valid.minGroup K₁),
      (e6Isogeny K₁ s : ModGL Tag.E6 K₁) ∈
        ((E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧
      (e6Isogeny K₁ t : ModGL Tag.E6 K₁) ∈
        ((E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧ s * t ≠ t * s := by
    unfold TwistedE6DiagIsotropic at hnoniso
    push Not at hnoniso
    exact hnoniso
  obtain ⟨s, t, hs, ht, hst⟩ := hnoniso'
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, hs1⟩ := hs
  obtain ⟨_, ⟨g₂, hg₂, rfl⟩, ht1⟩ := ht
  have hg₁3 : g₁ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) _ hg₁)
  have hg₂3 : g₂ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) _ hg₂)
  have hcomm₀ : g₁ * g₂ = g₂ * g₁ := by
    refine hinj ?_
    have := congrArg Subtype.val
      (hE.is_comm.comm ⟨twistedE6InndiagConj K σ g₁, hg₁⟩ ⟨twistedE6InndiagConj K σ g₂, hg₂⟩)
    rw [map_mul, map_mul]
    exact this
  have hd₁3 : (g₁ : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₁3
  have hd₂3 : (g₂ : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₂3
  have hcomm : (g₁ : ModGL TwistTag.E6.tag K) * g₂ = g₂ * g₁ := by
    simpa using congrArg Subtype.val hcomm₀
  obtain ⟨c₂, hc₂, a, b, w, ha3, hw, hsh, hca, hcb⟩ :=
    E6Heis.pair_normal_form_tw h3K K₁ (g₁ : ModGL TwistTag.E6.tag K)
      (g₂ : ModGL TwistTag.E6.tag K) (twistedE6InndiagGL_le_e6InndiagGL K σ g₁.2)
      (twistedE6InndiagGL_le_e6InndiagGL K σ g₂.2) hd₁3 hd₂3 hcomm s t hs1.symm ht1.symm hst
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι₀ : K →+* L := algebraMap K L with hι₀
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have hFix : twistHom TwistTag.E6 L Fr (baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K)) =
      baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K) :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1
      (map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ Fr hFr
        (Subgroup.mem_map_of_mem _ g₁.2))).2
  have hga : (c₂⁻¹)⁻¹ * baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K) * c₂⁻¹ =
      rootDiagUnit TwistTag.E6.tag a := by
    rw [inv_inv]
    exact hca
  obtain ⟨w', z, hz, hu, hga', hT⟩ :=
    E6Heis.lang_step_single_tw (L := L) (ℓ := ℓ) f hf (inv_mem hc₂) a ha3 hga hFix
  have hzC : z ∈ adjointGroup TwistTag.E6.tag L :=
    sup_le torusGroup_le_adjointGroup' (rootSpan_le_adjointGroup L _) hz
  have hg0C : c₂⁻¹ * z ∈ adjointGroup TwistTag.E6.tag L := mul_mem (inv_mem hc₂) hzC
  obtain ⟨u, b', hu', hconj⟩ := E6Heis.exists_rootSpan_conj_form a b w (m := z) hz
  have hg₂' : (c₂⁻¹ * z)⁻¹ * baseChangeGL ι₀ (g₂ : ModGL TwistTag.E6.tag K) * (c₂⁻¹ * z) =
      u⁻¹ * (rootDiagUnit Tag.E6 b' * canonicalRep (coxeterSystem Tag.E6) L w) * u := by
    have e1 : (c₂⁻¹ * z)⁻¹ * baseChangeGL ι₀ (g₂ : ModGL TwistTag.E6.tag K) * (c₂⁻¹ * z) =
        z⁻¹ * (c₂ * baseChangeGL ι₀ (g₂ : ModGL TwistTag.E6.tag K) * c₂⁻¹) * z := by group
    rw [e1, hcb]
    exact hconj
  have hker : ∀ g g' : ↥(e6Data_valid.minGroup K₁),
      ((e6Isogeny K₁ g : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ g' : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) →
      g'⁻¹ * g ∈ Subgroup.center ↥(e6Data_valid.minGroup K₁) := by
    intro g g' hgg'
    rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
    rw [MonoidHom.mem_ker]
    change e6Isogeny K₁ (g'⁻¹ * g) = 1
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact Subtype.ext hgg'.symm
  have hnot : ∀ k : ℤ, g₂ ≠ g₁ ^ k := by
    intro k hk
    apply hst
    have hπ : ((e6Isogeny K₁ t : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ (s ^ k) : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) := by
      rw [← ht1, hk, map_zpow (e6Isogeny K₁) s k, Subgroup.coe_zpow, ← hs1]
      simp [map_zpow]
      <;> rfl
    have hz1 := hker t (s ^ k) hπ
    have hsz : Commute s ((s ^ k)⁻¹ * t) := Subgroup.mem_center_iff.1 hz1 s
    have hsk : Commute s (s ^ k) := (Commute.refl s).zpow_right k
    have hct : Commute s t := by
      have := hsk.mul_right hsz
      rwa [mul_inv_cancel_left] at this
    exact hct.eq
  have he₁1 : twistedE6InndiagConj K σ g₁ ≠ 1 := by
    intro h
    have hg1 : g₁ = 1 := hinj (h.trans (map_one _).symm)
    have hπ : ((e6Isogeny K₁ s : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ (1 : ↥(e6Data_valid.minGroup K₁)) : adjointGroup Tag.E6 K₁) :
          ModGL Tag.E6 K₁) := by
      rw [← hs1, hg1]
      simp
      <;> rfl
    have hz1 := hker s 1 hπ
    have hs_c : s ∈ Subgroup.center ↥(e6Data_valid.minGroup K₁) := by simpa using hz1
    exact hst (Subgroup.mem_center_iff.1 hs_c t).symm
  have he₂n : twistedE6InndiagConj K σ g₂ ∉ Subgroup.zpowers (twistedE6InndiagConj K σ g₁) := by
    rintro ⟨k, hk⟩
    apply hnot k
    apply hinj
    rw [map_zpow]
    exact hk.symm
  have hgen : E = Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂} := by
    have hle : Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂} ≤ E := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hg₁
      · exact hg₂
    have hz₁ : Subgroup.zpowers (twistedE6InndiagConj K σ g₁) ≤
        Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂} := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    have he₂c : twistedE6InndiagConj K σ g₂ ∈
        Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have he₁o : orderOf (twistedE6InndiagConj K σ g₁) = 3 := by
      refine orderOf_eq_prime ?_ he₁1
      rw [← map_pow, hg₁3, map_one]
    have hc1 : Nat.card (Subgroup.zpowers (twistedE6InndiagConj K σ g₁)) = 3 := by
      rw [Nat.card_zpowers, he₁o]
    have hdvd1 : 3 ∣ Nat.card (Subgroup.closure
        {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂}) := by
      rw [← hc1]
      exact Subgroup.card_dvd_of_le hz₁
    have hdvd2 : Nat.card (Subgroup.closure
        {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂}) ∣ 3 ^ 2 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle
    have hne : Subgroup.zpowers (twistedE6InndiagConj K σ g₁) ≠
        Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂} := fun h =>
      he₂n (h ▸ he₂c)
    have hne3 : Nat.card (Subgroup.closure
        {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂}) ≠ 3 := by
      intro h3'
      apply hne
      exact Subgroup.eq_of_le_of_card_ge hz₁ (by rw [hc1, h3'])
    have h9 : Nat.card (Subgroup.closure
        {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂}) = 3 ^ 2 := by
      have := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd2
      obtain ⟨m, hm, hm'⟩ := this
      interval_cases m
      · rw [hm', pow_zero] at hdvd1
        omega
      · exact absurd (by rw [hm']; norm_num) hne3
      · exact hm'
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hcard])).symm
  exact ⟨⟨w', Fr, hFr, c₂⁻¹ * z, hg0C, hu, a, b', w, ha3, hw, hsh, hT, u, hu', g₁, g₂, hga', hg₂',
    hg₁, hg₂, hgen⟩⟩


end CFSG.LieType.SeitzGeneration.ExcWideThree

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality


end CFSG.LieType.SeitzGeneration.ExcWideThree
