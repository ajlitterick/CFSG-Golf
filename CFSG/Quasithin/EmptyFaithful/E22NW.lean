module

public import CFSG.Quasithin.EmptyFaithful.E22NParam

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

namespace E2

variable {Γ : Type} [Group Γ]

@[expose] def E22NParamWCases (H T M K : Subgroup Γ) : Prop :=
  let Ks := star M H K
  let MKs := star M H (M ⊓ K)
  let TKs := star M H (T ⊓ K)
  let Ts := star M H T
  let Q := pCoreOf 2 H
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (StarQuot M H))
  (kerIn M H = Q → (∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T) →
    ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 ↥Ks →
      MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) → 8 < autCard Ts Ks →
      E1.nParam H = 1) ∧
  (T ≤ Subgroup.normalizer (K : Set Γ) →
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) →
    (∀ n : ℕ, 1 ≤ n → (IsPSL 3 2 n ↥Ks ∨ IsSp4Prime n ↥Ks) → IsDiagramNontrivial Ts Ks TKs →
        IsBorelIn Ks MKs → n = 1 → E1.nParam H ≤ 1) ∧
      (∀ p e : ℕ, p.Prime → 3 < p → (e = 1 ∨ e = 2) → (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) →
        IsPSL 2 p e ↥Ks → MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) →
        8 < autCard Ts Ks → E1.nParam H = 1) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 →
        ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥Ks) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥Ks ∧ InducesOuter Ts Ks)) →
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) → E1.nParam H = 1))

@[expose] def E22NParamW : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M K : Subgroup Γ), MinParabolic H T M → SQTKGroup ↥H →
    ¬ Group.IsSolvable ↥H → K ∈ cComp H → H = K ⊔ T →
    CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) → E22CasesNoN H T M K →
    SQTKGroup (StarQuot M H) → E22NParamWCases H T M K

@[expose] def E22StatementW : Prop :=
  E22StatementNoN ∧ E22NParamW

theorem E22StatementW.toNoN (h : E22StatementW) : E22StatementNoN :=
  h.1

theorem E22StatementW.toNParam (h : E22StatementW) : E22NParamW :=
  h.2

theorem e22NParamWCases_of_e22NParamCases {H T M K : Subgroup Γ} (h : E22NParamCases H T M K) :
    E22NParamWCases H T M K := by
  dsimp only [E22NParamCases] at h
  dsimp only [E22NParamWCases]
  refine ⟨fun hJ ht p hp hp8 hK hMK haut => (h.1 hJ ht).2 p hp hp8 hK hMK haut,
    fun hTK hJ => ?_⟩
  obtain ⟨-, hb, hc, hd⟩ := h.2 hTK hJ
  refine ⟨fun n hn hty hD hB hn1 => ?_, hc, hd⟩
  have := (hb n hn hty hD hB).1
  subst hn1
  simpa using this

theorem E22StatementC.toW (h : E22StatementC) : E22StatementW :=
  ⟨h.toNoN, fun Γ _ _ H T M K hmin hSQ hns hKc hHK hq hc hSQs =>
    e22NParamWCases_of_e22NParamCases (h.toNParam Γ H T M K hmin hSQ hns hKc hHK hq hc hSQs)⟩

@[expose] def E22CasesW (H T M K : Subgroup Γ) : Prop :=
  let Ks := star M H K
  let MKs := star M H (M ⊓ K)
  let TKs := star M H (T ⊓ K)
  let Ts := star M H T
  let Q := pCoreOf 2 H
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (StarQuot M H))
  (kerIn M H = Q ∧ ∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T ∧
    ((∃ n : ℕ, 2 ≤ n ∧ (IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks) ∧ IsBorelIn Ks MKs) ∨
      (∃ p : ℕ, p.Prime ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧ IsPSL 2 p 1 ↥Ks ∧
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧ 8 < autCard Ts Ks ∧
        E1.nParam H = 1))) ∨
  (T ≤ Subgroup.normalizer (K : Set Γ) ∧
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) ∧
    ((∃ n : ℕ, IsBenderOf n ↥Ks ∧ IsBorelIn Ks MKs) ∨
      (∃ n : ℕ, 1 ≤ n ∧ (IsPSL 3 2 n ↥Ks ∨ IsSp4Prime n ↥Ks) ∧ IsDiagramNontrivial Ts Ks TKs ∧
        IsBorelIn Ks MKs ∧ (n = 1 → E1.nParam H ≤ 1)) ∨
      (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
        IsPSL 2 p e ↥Ks ∧ MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧
        8 < autCard Ts Ks ∧ E1.nParam H = 1) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥Ks) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥Ks ∧ InducesOuter Ts Ks)) ∧
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧ E1.nParam H = 1)))

theorem e22CasesW_of_noN {H T M K : Subgroup Γ} (hc : E22CasesNoN H T M K)
    (hn : E22NParamWCases H T M K) : E22CasesW H T M K := by
  dsimp only [E22CasesNoN] at hc
  dsimp only [E22NParamWCases] at hn
  dsimp only [E22CasesW]
  rcases hc with ⟨hJ, t, ht, hne, hM, h1⟩ | ⟨hTK, hJ, h2⟩
  · refine Or.inl ⟨hJ, t, ht, hne, hM, ?_⟩
    rcases h1 with ⟨n, hn2, hty, hB⟩ | ⟨p, hp, hp8, hK, hMK, haut⟩
    · exact Or.inl ⟨n, hn2, hty, hB⟩
    · exact Or.inr ⟨p, hp, hp8, hK, hMK, haut,
        hn.1 hJ ⟨t, ht, hne, hM⟩ p hp hp8 hK hMK haut⟩
  · obtain ⟨hb, hc', hd⟩ := hn.2 hTK hJ
    refine Or.inr ⟨hTK, hJ, ?_⟩
    rcases h2 with ⟨n, hBen, hB⟩ | ⟨n, h1n, hty, hD, hB⟩ |
        ⟨p, e, hp, hp3, he, hpe, hK, hMK, haut⟩ | ⟨p, hp, hp2, hK, hMK⟩
    · exact Or.inl ⟨n, hBen, hB⟩
    · exact Or.inr (Or.inl ⟨n, h1n, hty, hD, hB, hb n h1n hty hD hB⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe, hK, hMK, haut,
        hc' p e hp hp3 he hpe hK hMK haut⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨p, hp, hp2, hK, hMK, hd p hp hp2 hK hMK⟩))

end E2

namespace E2.E22StatementW

theorem exists_cases (h : E2.E22StatementW) {G : Type} [Group G] [Finite G]
    {H T M : Subgroup G} (hmin : MinParabolic H T M) (hSQ : SQTKGroup ↥H)
    (hns : ¬ Group.IsSolvable ↥H) :
    (∃ K : Subgroup G, K ∈ cComp H ∧ H = K ⊔ T ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ E2.E22CasesW H T M K) ∧
    SQTKGroup (E2.StarQuot M H) := by
  obtain ⟨⟨K, hKc, hHK, hq, hc⟩, hSQs⟩ := h.toNoN G H T M hmin hSQ hns
  exact ⟨⟨K, hKc, hHK, hq,
    E2.e22CasesW_of_noN hc (h.toNParam G H T M K hmin hSQ hns hKc hHK hq hc hSQs)⟩, hSQs⟩

end E2.E22StatementW

namespace E2.E22N


end E2.E22N

end CFSG.Quasithin
