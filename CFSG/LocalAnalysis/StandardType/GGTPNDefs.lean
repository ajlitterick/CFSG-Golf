module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Datum

@[expose] def GGTPNLocal (p : ℕ) {X : Type*} [Group X] (A : Subgroup (MulAut X)) (σ : MulAut X)
    (J : Subgroup X) : Prop :=
  (IsElemAbelian p A ∧ σ ∈ A ∧ σ ≠ 1 ∧ IsComponentOf J (ggAutFixedSubgroup σ) ∧
    ∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
    ∀ a ∈ A, (∀ j ∈ J, a j = j) → a ∈ Subgroup.zpowers σ

theorem ggTPNLocal_three {X : Type*} [Group X] {A : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} : GGTPNLocal 3 A σ J ↔ GGKLocal A σ J :=
  Iff.rfl

@[expose] def GGTPNLocalCore (p : ℕ) {X : Type*} [Group X] (A : Subgroup (MulAut X))
    (σ : MulAut X) (J : Subgroup X) : Prop :=
  IsElemAbelian p A ∧ σ ∈ A ∧ σ ≠ 1 ∧ IsComponentOf J (ggAutFixedSubgroup σ) ∧
    ∀ a ∈ A, ∀ j ∈ J, a j ∈ J

@[expose] def GGTPNKernel {X : Type*} [Group X] (A : Subgroup (MulAut X)) (σ : MulAut X)
    (J : Subgroup X) : Prop :=
  ∀ a ∈ A, (∀ j ∈ J, a j = j) → a ∈ Subgroup.zpowers σ


@[expose] def GGTPNRank (p : ℕ) (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) : Prop :=
  ∃ m : ℕ, Nat.card A = p ^ m ∧
    LargeEvenTwoLocalRank p X ≤ m + (if p ∣ Nat.card (Subgroup.center X) then 1 else 0)

@[expose] def GGTPNSelfCent (p : ℕ) {X : Type*} [Group X] (A : Subgroup (MulAut X)) : Prop :=
  ∀ t : X, (∀ a ∈ A, a t = t) → t ^ p = 1 → (MulAut.conj t : MulAut X) ∈ A

@[expose] def GGTPNOnlyComp (p : ℕ) {X : Type*} [Group X] [Finite X] (σ : MulAut X)
    (J : Subgroup X) : Prop :=
  ∀ J' : Subgroup X, LargeEvenPComponent p (ggAutFixedSubgroup σ) J' → J' = J

@[expose] def GGTPNMarked (p : ℕ) (S : ℕ → LargeEvenLabel → Prop) {X : Type} [Group X]
    (A : Subgroup (MulAut X)) : Prop :=
  LargeEvenMarking X fun lab _ _ I _ θ =>
    S p lab ∧ LargeEvenHalfSplit p lab (Subgroup.center X = ⊥) ∧ GGInducedInn A θ I

@[expose] def GGTPNHalfJ (p : ℕ) {X : Type*} [Group X] (J : Subgroup X) : Prop :=
  LargeEvenMarking ↥J fun lab _ _ _ _ _ => LargeEvenHalfSplit p lab (Subgroup.center ↥J = ⊥)

@[expose] def GGTPNRankOne (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank = 1) ∨ (lab.tag = .twD ∧ lab.rank = 2)

@[expose] def GGTPNRankJ {X : Type} [Group X] (J : Subgroup X) : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) →
    ¬ GGTPNRankOne lab

@[expose] def GGTPNCorners (p : ℕ) {X : Type} [Group X] (J : Subgroup X) : Prop :=
  (p = 7 → GGHasLabel ⟨.E6, 0, 1⟩ (X ⧸ Subgroup.center X) → GGTPNHalfJ p J) ∧
    (p = 3 → ∀ n : ℕ, GGHasLabel ⟨.twA, 5, n⟩ (X ⧸ Subgroup.center X) → GGTPNRankJ J)

@[expose] def GGTPNBasic (p : ℕ) (S : ℕ → LargeEvenLabel → Prop) {X : Type} [Group X] [Finite X]
    (A : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X) : Prop :=
  GGTPNLocal p A σ J ∧ p ^ 3 ≤ Nat.card A ∧ GGTPNRank p X A ∧ GGTPNSelfCent p A ∧
    GGTPNOnlyComp p σ J ∧ GGTPNMarked p S A

@[expose] def GGTPNDatum (p : ℕ) (S : ℕ → LargeEvenLabel → Prop) {X : Type} [Group X] [Finite X]
    (A : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X) : Prop :=
  GGTPNBasic p S A σ J ∧ GGTPNCorners p J

@[expose] def GGTPNFlat (p : ℕ) {X : Type*} [Group X] (A Ab : Subgroup (MulAut X))
    (σ : MulAut X) (J : Subgroup X) : Prop :=
  Ab ≤ A ∧ σ ∈ Ab ∧ Nat.card A ≤ p * Nat.card Ab ∧ GGTPNKernel Ab σ J

@[expose] def GGTPNNum (p n : ℕ) {X : Type*} [Group X] (A Ab : Subgroup (MulAut X)) : Prop :=
  p * Nat.card A ≤ n ∧ n ≤ p ^ 2 * Nat.card Ab

@[expose] def GGTPNBasicB (p n : ℕ) (S : ℕ → LargeEvenLabel → Prop) {X : Type} [Group X]
    [Finite X] (A Ab : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X) : Prop :=
  GGTPNLocalCore p A σ J ∧ GGTPNFlat p A Ab σ J ∧ p ^ 3 ≤ Nat.card Ab ∧ GGTPNRank p X Ab ∧
    GGTPNNum p n A Ab ∧ GGTPNSelfCent p A ∧ GGTPNOnlyComp p σ J ∧ GGTPNMarked p S A

@[expose] def GGTPNDatumB (p n : ℕ) (S : ℕ → LargeEvenLabel → Prop) {X : Type} [Group X]
    [Finite X] (A Ab : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X) : Prop :=
  GGTPNBasicB p n S A Ab σ J ∧ GGTPNCorners p J

@[expose] def GGTPNRow (p : ℕ) {X : Type} [Group X] (J : Subgroup X) : Prop :=
  ∃ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
    GGTablePRow p labJ labX ∧ GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧
    GGHasLabel labX (X ⧸ Subgroup.center X)

@[expose] def GGTablePKnownOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X))
    (σ : MulAut X) (J : Subgroup X), GGTPNDatum p S A σ J → GGTPNRow p J

@[expose] def GGTablePKnownR (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (A Ab : Subgroup (MulAut X))
    (σ : MulAut X) (J : Subgroup X) (n : ℕ), GGTPNDatumB p n (fun _ _ => True) A Ab σ J →
    ∀ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labX →
      R p n labJ labX → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
      GGHasLabel labX (X ⧸ Subgroup.center X) → GGTPNRow p J

@[expose] def GGTablePKnownRK (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (A Ab : Subgroup (MulAut X))
    (σ : MulAut X) (J : Subgroup X) (n : ℕ), GGTPNDatumB p n (fun _ _ => True) A Ab σ J →
    GGTPNKernel A σ J → ∀ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ →
      LargeEvenInLambda2 labX → R p n labJ labX → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
      GGHasLabel labX (X ⧸ Subgroup.center X) → GGTPNRow p J


end Datum

section Regimes

theorem ggTPNMarked_mono {p : ℕ} {S S' : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X]
    {A : Subgroup (MulAut X)} (hS : ∀ q lab, S q lab → S' q lab) (h : GGTPNMarked p S A) :
    GGTPNMarked p S' A := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  exact ⟨hX, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, h1, h2⟩ => ⟨hs, hna, θ, hS _ _ h1, h2⟩) hraw⟩

theorem ggTPNMarked_split {p : ℕ} {S₁ S₂ : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X]
    {A : Subgroup (MulAut X)} (h : GGTPNMarked p (fun q lab => S₁ q lab ∨ S₂ q lab) A) :
    GGTPNMarked p S₁ A ∨ GGTPNMarked p S₂ A := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hS, -⟩ := largeEvenRawDatum_exists hraw
  rcases hS with hs | hs
  · exact Or.inl ⟨hX, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs', hna, θ', _, h2⟩ => ⟨hs', hna, θ', hs, h2⟩) hraw⟩
  · exact Or.inr ⟨hX, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs', hna, θ', _, h2⟩ => ⟨hs', hna, θ', hs, h2⟩) hraw⟩

theorem GGTablePKnownOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ q lab, S q lab → S' q lab) (h : GGTablePKnownOn S') : GGTablePKnownOn S :=
  fun p hp hp2 X _ _ A σ J ⟨⟨hloc, hcard, hrank, hself, honly, hm⟩, hcor⟩ =>
    h p hp hp2 X A σ J ⟨⟨hloc, hcard, hrank, hself, honly, ggTPNMarked_mono hS hm⟩, hcor⟩

theorem GGTablePKnownOn.union {S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGTablePKnownOn S₁) (h₂ : GGTablePKnownOn S₂) :
    GGTablePKnownOn fun q lab => S₁ q lab ∨ S₂ q lab :=
  fun p hp hp2 X _ _ A σ J ⟨⟨hloc, hcard, hrank, hself, honly, hm⟩, hcor⟩ =>
    (ggTPNMarked_split hm).elim
      (fun hm₁ => h₁ p hp hp2 X A σ J ⟨⟨hloc, hcard, hrank, hself, honly, hm₁⟩, hcor⟩)
      (fun hm₂ => h₂ p hp hp2 X A σ J ⟨⟨hloc, hcard, hrank, hself, honly, hm₂⟩, hcor⟩)


end Regimes

section Transfer

theorem ggInnerDiagOn_le_normalizer {G : Type} [Group G] {Bs K : Subgroup G}
    (h : GGInnerDiagOn Bs K) : Bs ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨-, lab, -, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hN, -⟩ := largeEvenRawDatum_exists hraw
  exact hN


@[expose] def GGTPNTrLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (hx : x ∈ Subgroup.normalizer (K : Set G)),
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      GGTPNLocal p (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)

@[expose] def GGTPNTrLocalCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (hx : x ∈ Subgroup.normalizer (K : Set G)),
      GGTPNLocalCore p (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)

@[expose] def GGTPNTrFlat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hc : GGConfig p B Bs x L D J), GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (hx : x ∈ Subgroup.normalizer (K : Set G)),
      GGTPNFlat p (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN))
        (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)


@[expose] def GGTPNTrCardB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hc : GGConfig p B Bs x L D J), GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      p ^ 3 ≤ Nat.card (ggAutsOf K B (hc.2.1.1.trans hN))

@[expose] def GGTPNTrRankB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hc : GGConfig p B Bs x L D J), GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      GGTPNRank p K (ggAutsOf K B (hc.2.1.1.trans hN))

@[expose] def GGTPNTrNum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hc : GGConfig p B Bs x L D J), GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      GGTPNNum p (Nat.card Bs) (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN))

@[expose] def GGTPNTrSelfCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)), GGTPNSelfCent p (ggAutsOf K Bs hN)

@[expose] def GGTPNTrOnly : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hJK : J ≤ K) (hx : x ∈ Subgroup.normalizer (K : Set G)),
      GGTPNOnlyComp p (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)

@[expose] def GGTPNTrMarked : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      GGTPNMarked p (fun _ _ => True) (ggAutsOf K Bs hN)


theorem ggHasLabel_quotCenter_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {lab : LargeEvenLabel} (h : GGHasLabel lab (A ⧸ Subgroup.center A)) :
    GGHasLabel lab (B ⧸ Subgroup.center B) :=
  ggHasLabel_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (by
      ext b
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (mem_center_iff_of_mulEquiv e a).2 ha
      · intro hb
        exact ⟨e.symm b, (mem_center_iff_of_mulEquiv e _).1 (by simpa using hb), by simp⟩)) h


end Transfer

section A8Leaf

@[expose] def GGTablePA8SevenKnown : Prop :=
  ∀ (x : Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))
    (E J : Subgroup (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))),
    orderOf x = 7 → x ∈ E → IsElemAbelian 7 E → 7 ^ 3 ≤ Nat.card E →
    IsComponentOf J
      (Subgroup.centralizer ({x} : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))) →
    E ≤ Subgroup.normalizer (J : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))) →
    E ⊓ Subgroup.centralizer (J : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))) =
      Subgroup.zpowers x →
    (∀ J' : Subgroup (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)),
      IsComponentOf J' (Subgroup.centralizer
        ({x} : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))) → 7 ∣ Nat.card J' → J' = J) →
    GGHasLabel ⟨.A, 2, 3⟩ (J ⧸ Subgroup.center J) ∨ GGHasLabel ⟨.A, 5, 1⟩ (J ⧸ Subgroup.center J)

end A8Leaf

end CFSG.StandardType

end
