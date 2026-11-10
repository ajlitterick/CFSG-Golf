module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestFrame
public import CFSG.LocalAnalysis.StandardType.GGWeylCasePrime
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.RankThree.PartTwo.Sec21 Matrix

section Weyl

variable {G : Type} [Group G]

@[expose] def GGWeylOfType (p : ℕ) {Bs : Subgroup G} {ι : Type} (M : CoxeterMatrix ι)
    (A : Subgroup (MulAut ↥Bs)) : Prop :=
  ∃ e : M.Group ≃* ↥A, ∀ i : ι, GGIsReflection p ((e (M.simple i) : ↥A) : MulAut ↥Bs)

theorem GGWeylOfType.of_reindex {p : ℕ} {Bs : Subgroup G} {ι ι' : Type} {M : CoxeterMatrix ι}
    {e : ι ≃ ι'} {A : Subgroup (MulAut ↥Bs)} (h : GGWeylOfType p (M.reindex e) A) :
    GGWeylOfType p M A := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(M.reindexGroupEquiv e).symm.trans f, fun i => ?_⟩
  have e1 : ((M.reindexGroupEquiv e).symm.trans f) (M.simple i) = f ((M.reindex e).simple (e i)) :=
    rfl
  rw [e1]
  exact hf (e i)

theorem ggWeylReflectionGroup_cases {p : ℕ} {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (h : GGWeylReflectionGroup p A) :
    (∃ n, 1 ≤ n ∧ GGWeylOfType p (CoxeterMatrix.A n) A) ∨
      (∃ n, 2 ≤ n ∧ GGWeylOfType p (CoxeterMatrix.B n) A) ∨
      (∃ n, 4 ≤ n ∧ GGWeylOfType p (ggCoxeterMatrixD n) A) ∨
      GGWeylOfType p CoxeterMatrix.E₆ A ∨ GGWeylOfType p CoxeterMatrix.E₇ A ∨
      GGWeylOfType p CoxeterMatrix.E₈ A ∨ GGWeylOfType p CoxeterMatrix.F₄ A ∨
      GGWeylOfType p CoxeterMatrix.G₂ A := by
  obtain ⟨ι, M, hM, f, hf⟩ := h
  have hW : GGWeylOfType p M A := ⟨f, hf⟩
  rcases hM with ⟨n, e, hn, rfl | ⟨hn2, rfl⟩ | ⟨hn4, rfl⟩⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ |
    ⟨e, rfl⟩ | ⟨e, rfl⟩
  · exact Or.inl ⟨n, hn, hW.of_reindex⟩
  · exact Or.inr (Or.inl ⟨n, hn2, hW.of_reindex⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn4, hW.of_reindex⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hW.of_reindex)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hW.of_reindex))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hW.of_reindex)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hW.of_reindex))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hW.of_reindex))))))

end Weyl

section Config

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSecFiveRestHyp (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧ GGInnerDiagAll p B Bs x L D J ∧
    GGNoTransvection p Bs ∧
    (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs) →
      GGScalarsOrWeyl' p B Bs x D J →
        GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) ∧
    ¬ ∃ n f : ℕ, GGTypeASplitConfig p B Bs x L D J n f

@[expose] def GGSecFiveWeylCase (p : ℕ) (B Bs : Subgroup G) (x : G) (D J : Subgroup G) : Prop :=
  GGScalarsPmOne Bs ∧ ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
    GGReflGenerated p (ggAutomizer K Bs)

@[expose] def GGSecFiveWeylAt (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) {ι : Type}
    (M : CoxeterMatrix ι) : Prop :=
  ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
    GGWeylOfType p M (ggAutomizer L Bs ⊔ ggAutomizer K Bs)

theorem ggSecFiveAllAJoin_iff {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} :
    GGSecFiveAllAJoin p B Bs x L D J ↔ ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∃ m : ℕ, 1 ≤ m ∧ GGWeylOfType p (CoxeterMatrix.A m) (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
  Iff.rfl

@[expose] def GGTypeANbr (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (n f : ℕ)
    (y : G) (K : Subgroup G) : Prop :=
  StatedClassicalModel (L ⧸ Subgroup.center L) .PSL (n + 1) 2 f ∧ p ∣ 2 ^ f - 1 ∧ 3 ≤ n ∧
    GGScalarsPmOne Bs ∧ GGNbr p B x D J y K ∧
    StatedClassicalModel (K ⧸ Subgroup.center K) .PSL (n + 1) 2 f ∧
    GGWeylOfType p (CoxeterMatrix.A (n + 1)) (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∧
    GGSecFiveAllAJoin p B Bs x L D J

theorem GGTypeANbr.splitConfig {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} {y : G} {K : Subgroup G} (h : GGTypeANbr p B Bs x L D J n f y K)
    (hp : ¬ p ∣ n + 3) : GGTypeASplitConfig p B Bs x L D J n f := by
  obtain ⟨hmod, hpq, hn, hsc, hnbr, hmodK, hW⟩ := h
  exact ⟨hmod, hpq, hn, hp, hsc, y, K, hnbr, hmodK, hW⟩

theorem GGSecFiveRestHyp.dvd_of_typeANbr {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp p B Bs x L D J) {n f : ℕ} {y : G}
    {K : Subgroup G} (h : GGTypeANbr p B Bs x L D J n f y K) : p ∣ n + 3 := by
  by_contra hp
  exact hR.2.2.2.2.2 ⟨n, f, h.splitConfig hp⟩

theorem GGSecFiveRestHyp.exists_nonA_weylAt {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp p B Bs x L D J)
    (hWC : GGSecFiveWeylCase' p B Bs x D J) (hAll : ¬ GGSecFiveAllAJoin p B Bs x L D J) :
    (∃ n, 2 ≤ n ∧ GGSecFiveWeylAt p B Bs x L D J (CoxeterMatrix.B n)) ∨
      (∃ n, 4 ≤ n ∧ GGSecFiveWeylAt p B Bs x L D J (ggCoxeterMatrixD n)) ∨
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₆ ∨
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₇ ∨
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₈ ∨
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.F₄ ∨
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.G₂ := by
  rw [ggSecFiveAllAJoin_iff] at hAll
  push Not at hAll
  obtain ⟨y, K, hnbr, hnA⟩ := hAll
  have hWK := hR.2.2.2.2.1 y K hnbr (hWC y K hnbr) (Or.inr hWC)
  rcases ggWeylReflectionGroup_cases hWK with ⟨n, hn, hT⟩ | ⟨n, hn, hT⟩ | ⟨n, hn, hT⟩ | hT | hT |
    hT | hT | hT
  · exact absurd hT (hnA n hn)
  · exact Or.inl ⟨n, hn, y, K, hnbr, hT⟩
  · exact Or.inr (Or.inl ⟨n, hn, y, K, hnbr, hT⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨y, K, hnbr, hT⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨y, K, hnbr, hT⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, K, hnbr, hT⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, K, hnbr, hT⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨y, K, hnbr, hT⟩)))))

@[expose] def GGTypeAHalfNbr (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (n : ℕ)
    (y : G) (K : Subgroup G) : Prop :=
  StatedClassicalModel (L ⧸ Subgroup.center L) .PSL (n + 1) 2 1 ∧ p = 3 ∧ 5 ≤ n ∧
    GGScalarsPmOne Bs ∧ GGNbr p B x D J y K ∧
    StatedClassicalModel (K ⧸ Subgroup.center K) .PSL (n + 1) 2 1 ∧
    ∃ r : ℕ, GGWeylOfType p (CoxeterMatrix.B r) (ggAutomizer L Bs ⊔ ggAutomizer K Bs)

end Config

@[expose] def GGTypeAJoinEndNodeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
    GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → GGTypeANbr p B Bs x L D J n f y K →
    ∀ φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L →
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      ∃ T : G, T ∈ L ⊔ K ∧ GGTypeAEndNode φ₁ T ∧ K ≤ L ⊔ L.map (MulAut.conj T).toMonoidHom


section TypeA

variable {G : Type} [Group G] [Finite G]

theorem GGTypeANbr.exists_lift {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} {y : G} {K : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (h : GGTypeANbr p B Bs x L D J n f y K) :
    1 ≤ f ∧ ∃ φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) := by
  obtain ⟨hmod, hpq, hn, -⟩ := h
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hf1 : 1 ≤ f := hmod.1.2.1
  have hf : 2 ≤ f := by
    by_contra hlt
    have hf' : f = 1 := by omega
    rw [hf'] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  have hperf : commutator L = ⊤ := hcfg.1.2.2.2.2.2.2.2.1.1
  exact ⟨hf1, exists_slLift_of_classicalModel (by omega) hf (by omega) hperf hmod⟩

theorem GGTypeANbr.sup_le_ggG0 {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} {y : G} {K : Subgroup G} (h : GGTypeANbr p B Bs x L D J n f y K) :
    L ⊔ K ≤ ggG0 p B x L D J :=
  sup_le (le_ggG0_left p B x L D J) (le_ggG0_of_ggNbr h.2.2.2.2.1)

theorem ggSecFiveTypeA_of_join (hE : GGTypeAJoinEndNodeInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (h : GGTypeANbr p B Bs x L D J n f y K)
    (hjoin : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ L ⊔ K) :
    GGSecFiveTypeA p B x L D J (n + 1) (n + 1) f := by
  obtain ⟨hf1, φ₁, hφL, hker⟩ := h.exists_lift hcfg
  obtain ⟨T, hTLK, hT, hKle⟩ := hE G p B Bs x L D J n f y K hcfg hOp hInn hNoTr h φ₁ hφL hker
  exact ggSecFiveTypeA_of_endNode h.2.2.1 hf1 φ₁ hφL hker hT (h.sup_le_ggG0 hTLK)
    (fun y' K' hK' => (hjoin y' K' hK').trans (sup_le le_sup_left hKle))


end TypeA

theorem ggTypeAEndNodeInput_of_joinEndNode (hE : GGTypeAJoinEndNodeInput)
    (hD : GGTypeAJoinInput) : GGTypeAEndNodeInput := by
  intro G _ _ p B Bs x L D J n f hcfg hOp hInn hNoTr hsplit φ₁ hφL hker
  obtain ⟨y, K, hN⟩ := exists_ggTypeASplitNbr hcfg hOp hInn hNoTr hsplit
  obtain ⟨-, -, -, -, hmod, hpq, hn, -, hsc, hnbr, hmodK, hW⟩ := id hN
  have hA : GGTypeANbr p B Bs x L D J n f y K := ⟨hmod, hpq, hn, hsc, hnbr, hmodK, hW⟩
  obtain ⟨T, hTLK, hT, hKle⟩ := hE G p B Bs x L D J n f y K hcfg hOp hInn hNoTr hA φ₁ hφL hker
  exact ⟨T, hA.sup_le_ggG0 hTLK, hT, fun y' K' hK' =>
    (hD G p B Bs x L D J n f y K hN y' K' hK').trans (sup_le le_sup_left hKle)⟩

section Input

@[expose] def GGSecFiveData {G : Type} [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (L D J : Subgroup G) : Prop :=
  (∃ m k f : ℕ, 4 ≤ k ∧ k ≤ m ∧ 1 ≤ f ∧ GGSecFiveTypeA p B x L D J m k f) ∨
    (∃ (t : StatedLieTag) (n f : ℕ), GGSecFiveLocal p B x L D J t n f) ∨
    (∃ (t : StatedLieTag) (n f : ℕ), GGSecFivePres p B x L D J t n f)

@[expose] def GGSecFiveNonWeylInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → ¬ GGSecFiveWeylCase' p B Bs x D J →
      GGSecFiveData p B x L D J

@[expose] def GGSecFiveWeylAInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      (∃ n, 1 ≤ n ∧ GGSecFiveWeylAt p B Bs x L D J (CoxeterMatrix.A n)) →
      (¬ ∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbr p B Bs x L D J n f y K) →
      GGSecFiveData p B x L D J

@[expose] def GGSecFiveWeylBInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      (∃ n, 2 ≤ n ∧ GGSecFiveWeylAt p B Bs x L D J (CoxeterMatrix.B n)) →
      (¬ ∃ (n : ℕ) (y : G) (K : Subgroup G), GGTypeAHalfNbr p B Bs x L D J n y K) →
      GGSecFiveData p B x L D J

@[expose] def GGSecFiveWeylDInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      (∃ n, 4 ≤ n ∧ GGSecFiveWeylAt p B Bs x L D J (ggCoxeterMatrixD n)) →
      GGSecFiveData p B x L D J

@[expose] def GGSecFiveWeylEInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      (GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₆ ∨
        GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₇ ∨
        GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₈) →
      GGSecFiveData p B x L D J

@[expose] def GGSecFiveWeylF4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.F₄ → GGSecFiveData p B x L D J

@[expose] def GGSecFiveWeylG2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.G₂ → GGSecFiveData p B x L D J


end Input

section Assembly


end Assembly

end CFSG.StandardType
