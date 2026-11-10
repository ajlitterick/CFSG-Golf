module

public import CFSG.Milestones.ASVolI.A1
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Small
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Sporadic
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.McL
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.U54
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Alt9
public import CFSG.Adapters.StatedPSLTwoNine
public import CFSG.LieType.SeitzGeneration.UnitaryHyperDiag
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Glue
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Main
public import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.RankThree.OddKernel.FailureReduction
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.LocalAnalysis.SectionRank.QTK.A134ListSL2
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Milestones.LR_rank_two_isomorphism_types
public import CFSG.RankThree.PartOne.KF.F128SL
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimePrimeCentralizer
public import CFSG.GH74.GLS.IVK.Proofs2.Std44LinConj
public import CFSG.GH74.GLS.IVK.Proofs2.Std44UniConj
public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.GLS.LU.Local.L3Cover
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerT
public import CFSG.Quasithin.Background.A3FactsNumber
public import CFSG.Milestones.ASVolI.I1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint
open CFSG.ASVolI.ChA

namespace ChA

@[expose] def IsSectionOf (S : Type*) [Group S] (G : Type*) [Group G] : Prop :=
  ∃ (H K : Subgroup G) (_ : (K.subgroupOf H).Normal), Nonempty (S ≃* ↥H ⧸ K.subgroupOf H)

@[expose] def IsProperSectionOf (S : Type*) [Group S] (G : Type*) [Group G] : Prop :=
  IsSectionOf S G ∧ Nat.card S < Nat.card G

@[expose] def TheoremAConclusion (G : Type) [Group G] [Finite G]
    (S : Type) [Group S] [Finite S] (p : ℕ) : Prop :=
  ((twoLocalPrimeRank p S ≤ twoLocalPrimeRank p G ∧ twoLocalPrimeRank p G ≤ 2) ∨
    (p = 3 ∧ ∃ (H H₁ H₂ : Subgroup G) (n₁ n₂ : ℕ),
      Nonempty (S ≃* ↥H ⧸ Subgroup.center ↥H) ∧ pRank 3 H = 3 ∧ H = H₁ ⊔ H₂ ∧
      IsComponentOf H₁ H ∧ IsComponentOf H₂ H ∧ IsSUn 3 (2 ^ n₁) ↥H₁ ∧ IsSUn 3 (2 ^ n₂) ↥H₂ ∧
      3 ≤ n₁ ∧ Odd n₁ ∧ 3 ≤ n₂ ∧ Odd n₂ ∧ centerOf H₁ = centerOf H₂ ∧
      (Nat.gcd n₁ n₂ = 1 ∨ Nat.gcd n₁ n₂ = 3))) ∧
  (pRank p (⊤ : Subgroup G) ≤ 2 → pRank p (⊤ : Subgroup S) ≤ pRank p (⊤ : Subgroup G))

@[expose] def TheoremAHolds (G : Type) [Group G] [Finite G] : Prop :=
  evenRank G ≤ 2 → CFSG.SectionRank.IsKGroupCat G →
    ∀ (S : Type) [Group S] [Finite S], IsSectionOf S G → genFittingLayer S = ⊤ →
      (∀ p : ℕ, p.Prime → p ≠ 2 → TheoremAConclusion G S p) ∧
      (CFSG.IsStronglyQuasithin G → CFSG.IsStronglyQuasithin S)

@[expose] def TheoremBList (G : Type) [Group G] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ n ≤ 9 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
  (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ (e = 1 ∨ e = 2) ∧
    (StatedClassicalModel G .PSL 3 p e ∨ StatedClassicalModel G .PSU 3 p e)) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    (StatedClassicalModel G .PSp 2 p 1 ∨ ChevalleyExceptionalModel G .G2 p 1)) ∨
  (∃ a r : ℕ, r = 2 ^ a + 1 ∧ r.Prime ∧ StatedClassicalModel G .PSL 4 r 1) ∨
  (∃ b s : ℕ, s = 2 ^ b - 1 ∧ s.Prime ∧ StatedClassicalModel G .PSU 4 s 1) ∨
  (∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel G .PSL 2 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel G .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel G .PSU 3 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel G .PSU 4 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel G .PSp 2 2 f) ∨
    (2 ≤ f ∧ ChevalleyExceptionalModel G .G2 2 f) ∨
    (1 ≤ f ∧ ChevalleyExceptionalModel G .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel G .twistedF4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ SuzukiModel G 2 f)) ∨
  ReeTitsModel G .Tits 2 1 ∨ StatedClassicalModel G .PSU 5 2 2 ∨
  StatedClassicalModel G .PSL 4 2 1 ∨ StatedClassicalModel G .PSL 5 2 1 ∨
  StatedClassicalModel G .PSp 3 2 1 ∨
  (∃ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J3 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .McL) ∧
    Nonempty (G ≃* NativeSporadic.Carrier s))

@[expose] def TheoremBHolds (G : Type) [Group G] [Finite G] : Prop :=
  IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → evenRank G ≤ 2 →
    CFSG.SectionRank.IsKGroupCat G → TheoremBList G

@[expose] def TheoremCHolds (G : Type) [Group G] [Finite G] : Prop :=
  IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → CFSG.SectionRank.IsSQTKCat G →
    CFSG.Milestones.SQTKSimpleList G

@[expose] def IsMinimalCounterexampleToA (G : Type) [Group G] [Finite G]
    (S : Type) [Group S] [Finite S] (p : ℕ) : Prop :=
  evenRank G ≤ 2 ∧ CFSG.SectionRank.IsKGroupCat G ∧ IsSectionOf S G ∧ genFittingLayer S = ⊤ ∧
  p.Prime ∧ p ≠ 2 ∧ ¬ TheoremAConclusion G S p ∧
  ∀ (X : Type) [Group X] [Finite X], IsProperSectionOf X G → TheoremAHolds X

@[expose] def IsMinimalCounterexampleABC (G : Type) [Group G] [Finite G] : Prop :=
  (¬ TheoremAHolds G ∨ ¬ TheoremBHolds G ∨ ¬ TheoremCHolds G) ∧
  ∀ (X : Type) [Group X] [Finite X], IsProperSectionOf X G →
    TheoremAHolds X ∧ TheoremBHolds X ∧ TheoremCHolds X

section LieAut

open CFSG.Blueprint.Chevalley

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def glMapAut (σ : K ≃+* K) : GL ι K →* GL ι K :=
  Units.map (RingHom.mapMatrix (σ : K →+* K)).toMonoidHom

@[expose] def IsProjFieldAut (H : Subgroup (GL ι K)) (σ : K ≃+* K)
    (φ : MulAut (StatedProj H)) : Prop :=
  ∀ g : ↥H, ∃ g' : ↥H, (g' : GL ι K) = glMapAut σ (g : GL ι K) ∧
    φ (QuotientGroup.mk g) = QuotientGroup.mk g'

@[expose] def IsProjConjAut (H : Subgroup (GL ι K)) (c : GL ι K)
    (φ : MulAut (StatedProj H)) : Prop :=
  ∀ g : ↥H, ∃ g' : ↥H, (g' : GL ι K) = c * g * c⁻¹ ∧
    φ (QuotientGroup.mk g) = QuotientGroup.mk g'

@[expose] def IsEvenLieThmC (S : Type) [Group S] : Prop :=
  (∃ n, StatedClassicalModel S .PSL 2 2 n) ∨ (∃ n, StatedClassicalModel S .PSL 3 2 n) ∨
  (∃ n, StatedClassicalModel S .PSU 3 2 n) ∨ (∃ n, StatedClassicalModel S .PSp 2 2 n) ∨
  (∃ n, ChevalleyExceptionalModel S .G2 2 n) ∨ (∃ n, ChevalleyExceptionalModel S .trialityD4 2 n) ∨
  (∃ n, SuzukiModel S 2 n) ∨ (∃ n, ReeTitsModel S .twistedF4 2 n) ∨ ReeTitsModel S .Tits 2 1 ∨
  StatedClassicalModel S .PSL 4 2 1 ∨ StatedClassicalModel S .PSL 5 2 1 ∨
  Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ StatedClassicalModel S .PSU 3 3 1

@[expose] def IsEvenLieAll (S : Type) [Group S] : Prop :=
  CFSG.Blueprint.EvenLieType S ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
    StatedClassicalModel S .PSU 3 3 1

@[expose] def IsFieldAut (S : Type) [Group S] (θ : MulAut S) : Prop :=
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* StatedProj (StatedSL 2 K))
      (σ : RingAut K), Nat.card K = 2 ^ n ∧ IsProjFieldAut (StatedSL 2 K) σ (MulAut.congr e θ)) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* StatedProj (StatedSL 3 K))
      (σ : RingAut K), Nat.card K = 2 ^ n ∧ IsProjFieldAut (StatedSL 3 K) σ (MulAut.congr e θ)) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (e : S ≃* StatedProj (StatedSU 3 (2 ^ n) K)) (σ : RingAut K), Nat.card K = (2 ^ n) ^ 2 ∧
        Odd (orderOf σ) ∧ IsProjFieldAut (StatedSU 3 (2 ^ n) K) σ (MulAut.congr e θ)) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* StatedProj (StatedSp 2 K))
      (σ : RingAut K), Nat.card K = 2 ^ n ∧ IsProjFieldAut (StatedSp 2 K) σ (MulAut.congr e θ)) ∨
  (∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* ↥(suzukiGroup a K))
      (σ : RingAut K), Nat.card K = 2 ^ (2 * a + 1) ∧
        ∀ g : ↥(suzukiGroup a K), ∃ g' : ↥(suzukiGroup a K),
          (g' : GL (Fin 4) K) = glMapAut σ (g : GL (Fin 4) K) ∧ MulAut.congr e θ g = g') ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* AdjointQuotient Tag.G2 K)
      (σ : RingAut K), Nat.card K = 2 ^ n ∧
        ∀ g : ↥(adjointGroup Tag.G2 K), ∃ g' : ↥(adjointGroup Tag.G2 K),
          (g' : ModGL Tag.G2 K) = Units.map (entrywiseHom (σ : K →+* K)) (g : ModGL Tag.G2 K) ∧
          MulAut.congr e θ (QuotientGroup.mk g) = QuotientGroup.mk g') ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (σq : K →+* K)
      (e : S ≃* DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σq)) (σ : RingAut K),
      Nat.card K = (2 ^ n) ^ 3 ∧ (∀ c, σq c = c ^ 2 ^ n) ∧ Nat.Coprime (orderOf σ) 3 ∧
        ∀ g : ↥⁅twistedFixedGroup TwistTag.D4 K σq, twistedFixedGroup TwistTag.D4 K σq⁆,
          ∃ g' : ↥⁅twistedFixedGroup TwistTag.D4 K σq, twistedFixedGroup TwistTag.D4 K σq⁆,
            (g' : ModGL TwistTag.D4.tag K) =
              Units.map (entrywiseHom (σ : K →+* K)) (g : ModGL TwistTag.D4.tag K) ∧
            MulAut.congr e θ (QuotientGroup.mk g) = QuotientGroup.mk g') ∨
  (∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (e : S ≃* DerivedCentralQuotient
        (reeFixedGroup Tag.F4 K reeF4Perm fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)))
      (σ : RingAut K), Nat.card K = 2 ^ (2 * a + 1) ∧
        ∀ g : ↥⁅reeFixedGroup Tag.F4 K reeF4Perm
            (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)),
            reeFixedGroup Tag.F4 K reeF4Perm
            (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))⁆,
          ∃ g' : ↥⁅reeFixedGroup Tag.F4 K reeF4Perm
            (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)),
            reeFixedGroup Tag.F4 K reeF4Perm
            (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))⁆,
            (g' : ModGL Tag.F4 K) =
              Units.map (entrywiseHom (σ : K →+* K)) (g : ModGL Tag.F4 K) ∧
            MulAut.congr e θ (QuotientGroup.mk g) = QuotientGroup.mk g') ∨
  (θ = 1 ∧ (StatedClassicalModel S .PSL 4 2 1 ∨ StatedClassicalModel S .PSL 5 2 1 ∨
    ReeTitsModel S .Tits 2 1 ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
    StatedClassicalModel S .PSU 3 3 1))

@[expose] def IsInnDiagAut (S : Type) [Group S] (ψ : MulAut S) : Prop :=
  ψ ∈ (MulAut.conj : S →* MulAut S).range ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* StatedProj (StatedSL 3 K))
      (c : GL (Fin 3) K), Nat.card K = 2 ^ n ∧ IsProjConjAut (StatedSL 3 K) c (MulAut.congr e ψ)) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (e : S ≃* StatedProj (StatedSU 3 (2 ^ n) K)) (c : GL (Fin 3) K), Nat.card K = (2 ^ n) ^ 2 ∧
        IsProjConjAut (StatedSU 3 (2 ^ n) K) c (MulAut.congr e ψ))

@[expose] def IsInnDiagFieldAut (S : Type) [Group S] (θ : MulAut S) : Prop :=
  ∃ ψ₁ ψ₂ : MulAut S, IsInnDiagAut S ψ₁ ∧ IsFieldAut S ψ₂ ∧ θ = ψ₁ * ψ₂

@[expose] def innDiagSubgroup (S : Type) [Group S] : Subgroup (MulAut S) :=
  Subgroup.closure {ψ | IsInnDiagAut S ψ}

end LieAut

end ChA

@[expose] def A_2_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 2 → CFSG.SectionRank.IsKGroupCat G →
    ∀ (S : Type) [Group S] [Finite S], IsSectionOf S G → genFittingLayer S = ⊤ →
      (∀ p : ℕ, p.Prime → p ≠ 2 → TheoremAConclusion G S p) ∧
      (CFSG.IsStronglyQuasithin G → CFSG.IsStronglyQuasithin S)


@[expose] def A_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    evenRank G ≤ 2 → CFSG.SectionRank.IsKGroupCat G → TheoremBList G

section BurnsideWA2


end BurnsideWA2

section


end

@[expose] def A_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.SectionRank.IsSQTKCat G →
    ∀ (L : Subgroup G) [L.Normal],
      CFSG.IsQuasisimple (↥L ⧸ pCore 2 ↥L) →
      IsEvenLieAll ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)) →
      IsEvenLieThmC ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)) ∧
      ∀ x : G, Odd (orderOf x) →
        ∃ θ : MulAut ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)),
          IsInnDiagFieldAut _ θ ∧
          ∀ l : ↥L, θ (QuotientGroup.mk (QuotientGroup.mk l)) =
            QuotientGroup.mk (QuotientGroup.mk (MulAut.conjNormal x l))

@[expose] def A_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) [K.Normal] (p : ℕ), p.Prime → p ≠ 2 →
    (pRank p (⊤ : Subgroup G) ≤ 1 → pRank p (⊤ : Subgroup (G ⧸ K)) ≤ pRank p (⊤ : Subgroup G)) ∧
    (twoLocalPrimeRank p G ≤ 1 → twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p G) ∧
    (pRank p (⊤ : Subgroup (G ⧸ K)) ≤ 2 →
      pRank p (⊤ : Subgroup (G ⧸ K)) ≤ pRank p (⊤ : Subgroup G)) ∧
    (twoLocalPrimeRank p (G ⧸ K) ≤ 2 → twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p G) ∧
    (pRank p (⊤ : Subgroup (G ⧸ K)) ≤ 2 →
      pRank p (⊤ : Subgroup (G ⧸ K)) ≤ pRank p (⊤ : Subgroup G) ∧
      twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p G)


@[expose] def A_2_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Type) [Group S] [Finite S] (p : ℕ),
    IsMinimalCounterexampleToA G S p →
    (∀ H : Subgroup G, IsSectionOf S ↥H → H = ⊤) ∧
    (∃ (K : Subgroup G) (_ : K.Normal), Nonempty (S ≃* G ⧸ K))

section BurnsideMA2


end BurnsideMA2


@[expose] def A_2_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Type) [Group S] [Finite S] (p : ℕ),
    IsMinimalCounterexampleToA G S p → pCore 2 G = ⊥


@[expose] def A_2_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Type) [Group S] [Finite S] (p : ℕ),
    IsMinimalCounterexampleToA G S p →
    Nonempty ((G ⧸ pCore p G) ≃* (S ⧸ Subgroup.center S))

section BurnsideTA11


section Cfg

variable {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S] {p : ℕ}


end Cfg

section Transfer


end Transfer

section SLBound


end SLBound

section ClauseB


end ClauseB

section R1

variable {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S] {p : ℕ}


end R1

section Misc

variable {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S] {p : ℕ}


end Misc

section Main

variable {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S] {p : ℕ}

section R3exc


end R3exc


end Main

section Orbit


end Orbit

section Models


end Models

section E4


end E4

section ModelS


end ModelS

section ModelNe


end ModelNe

section Small


end Small

section Embed


end Embed

section Dichotomy


end Dichotomy

end BurnsideTA11

section


end

@[expose] def A_2_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G → ¬ TheoremAHolds G →
    IsQuasisimple G

@[expose] def A_2_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    (IsSimpleGroup G ∧ (¬ TheoremBHolds G ∨ ¬ TheoremCHolds G)) ∨
    (IsQuasisimple G ∧ ¬ IsSimpleGroup G ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p (Subgroup.center G) ∧
      ∃ (Z : Subgroup G) (_ : Z.Normal), Z ≠ ⊥ ∧ Z ≤ Subgroup.center G ∧
        evenRank G ≤ 2 ∧ CFSG.SectionRank.IsKGroupCat G ∧ IsSectionOf (G ⧸ Z) G ∧
        genFittingLayer (G ⧸ Z) = ⊤ ∧ ¬ TheoremAConclusion G (G ⧸ Z) p ∧
        ∀ (q : ℕ), q.Prime → q ≠ 2 →
          ∀ (S : Type) [Group S] [Finite S], IsSectionOf S G → genFittingLayer S = ⊤ →
            ¬ TheoremAConclusion G S q → q = p)

@[expose] def A_2_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → IsPGroup p (Subgroup.center G) →
    ∀ (Z : Subgroup G) (_ : Z.Normal), Z ≠ ⊥ → Z ≤ Subgroup.center G →
      genFittingLayer (G ⧸ Z) = ⊤ → ¬ TheoremAConclusion G (G ⧸ Z) p →
      2 < pRank p (⊤ : Subgroup (G ⧸ Z)) ∧
      (Nat.card (Subgroup.center G) = p →
        2 < pRank p (⊤ : Subgroup (G ⧸ Subgroup.center G)))


@[expose] def A_2_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ∀ M : Subgroup G, M < ⊤ → ∀ (R : Type) [Group R] [Finite R], IsSectionOf R ↥M →
      genFittingLayer R = ⊤ → ∀ r : ℕ, r.Prime → r ≠ 2 →
      (pRank r (⊤ : Subgroup G) ≤ 2 →
        pRank r (⊤ : Subgroup R) ≤ pRank r M ∧ pRank r M ≤ pRank r (⊤ : Subgroup G)) ∧
      (IsTwoLocal M →
        pRank r (⊤ : Subgroup R) ≤ pRank r M ∧ pRank r M ≤ twoLocalPrimeRank r G ∧
          twoLocalPrimeRank r G ≤ 2) ∧
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        TheoremBList R ∧ (IsTwoLocal M → CFSG.Milestones.SQTKSimpleList R))


@[expose] def A_2_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty ((G ⧸ Subgroup.center G) ≃* alternatingGroup (Fin n))

@[expose] def A_2_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ¬ OddLieType (G ⧸ Subgroup.center G)

@[expose] def A_2_18 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ¬ EvenLieType (G ⧸ Subgroup.center G)

@[expose] def A_2_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ¬ NativeSporadic.SporadicRep (G ⧸ Subgroup.center G)

section TheoremAReduction

open CFSG.Open CFSG.Blueprint
open CFSG.ASVolI.ChA
open scoped commutatorElement


section RankDown

open CFSG.SectionRank.QTK CFSG.SectionRank.QTK.CentreFact Subgroup


end RankDown


section Main


end Main

section Final


end Final

end TheoremAReduction

section TheoremAReductionCentre


end TheoremAReductionCentre

section BurnsideTA12

section BurnsideTA12

open CFSG.ASVolI.ChA
open CFSG.Blueprint
open scoped commutatorElement


end BurnsideTA12

section BurnsideTA12cov

open CFSG.ASVolI.ChA
open CFSG.Blueprint
open scoped commutatorElement MatrixGroups


end BurnsideTA12cov

section BurnsideTA12pair

open CFSG.ASVolI.ChA
open Subgroup CFSG.SectionRank.QTK CFSG.SectionRank.QTK.CoverB CFSG.SectionRank.QTK.CentreFact


end BurnsideTA12pair


section


end

end BurnsideTA12

section TheoremAFinalA212


end TheoremAFinalA212

section TheoremAFinalA21


end TheoremAFinalA21

section TheoremAFinalVacuous


end TheoremAFinalVacuous

end CFSG.ASVolI
