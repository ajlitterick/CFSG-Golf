module

public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Item181_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    ∀ X : Subgroup G, A ≤ X → X ≠ ⊤ →
      inSubgroup (CFSG.pPrimeCore 3) X ≠ inSubgroup (CFSG.pPrimeCore 3) (X ⊓ M) →
      ∃ L ∈ oTwoComponentsIn X, ∃ S : Subgroup G,
        CFSG.ABGLocalTools.IsSylowOf 2 S (inSubgroup (CFSG.pPrimeCore 3) (X ⊓ M)) ∧
        L ⊔ A ⊔ S ∈ scriptH A M

@[expose] def Item181_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    ∀ H ∈ scriptH A M, ∃ s : G, Sec4.Concl4442 A M H s ∧
      CFSG.Open.pCoreOf 2 (H ⊓ M) = Subgroup.zpowers s ⊔ CFSG.Open.pCoreOf 2 H ∧
      (CFSG.Open.pCoreOf 2 H).relIndex (CFSG.Open.pCoreOf 2 (H ⊓ M)) = 2

@[expose] def Item181_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    ∀ H ∈ scriptH A M, CFSG.generalizedFitting H = CFSG.pCore 2 H →
      (∃ C : Subgroup (CFSG.Open.pCoreOf 2 (H ⊓ M)), C.Characteristic ∧ C ≠ ⊥ ∧
          H ≤ Subgroup.normalizer
            ((C.map (CFSG.Open.pCoreOf 2 (H ⊓ M)).subtype : Subgroup G) : Set G)) ∧
        (Nonempty (inSubgroup perfectResidual H ⧸
            CFSG.pCore 2 (inSubgroup perfectResidual H) ≃* projSL 3 (GaloisField 2 2)) →
          ThreeOfFourNormal H (fourChar (CFSG.Open.pCoreOf 2 (H ⊓ M))))

@[expose] def Item182 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    ∀ H ∈ scriptH A M, ∀ X : Subgroup G, H ≤ X → X ≠ ⊤ →
      ∃ K ∈ oTwoComponentsIn X, ¬ K ≤ M ∧
        K ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ∈ scriptH A M ∧
        (K = inSubgroup perfectResidual H ⊔ CFSG.Open.pCoreOf 2 K ∨
          (Nonempty (inSubgroup perfectResidual H ⧸
              CFSG.pCore 2 (inSubgroup perfectResidual H) ≃* projSL 3 (GaloisField 2 2)) ∧
            ∃ J ∈ thetaComponentsIn X, ⁅inSubgroup perfectResidual H, X⁆ = K ⊔ J ∧
              Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
              ((∃ n : ℕ, 1 ≤ n ∧ Nonempty (J ⧸ CFSG.pCore 2 J ≃*
                  Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * n)))) ∨
                Sec4.IsExtOf (J ⧸ CFSG.pCore 2 J) CFSG.Blueprint.NativeSporadic.M22
                  (Multiplicative (ZMod 3)))))


@[expose] def Item184_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    ∀ H ∈ scriptH A M,
      Nonempty (inSubgroup perfectResidual H ⧸
          CFSG.pCore 2 (inSubgroup perfectResidual H) ≃* projSL 3 (GaloisField 2 2)) ∧
        ∃ c : G, orderOf c = 3 ∧ sectionCentralizer A (inSubgroup perfectResidual H)
          (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H)) = (Subgroup.zpowers c : Set G)

@[expose] def Item184_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    let Lc := inSubgroup perfectResidual
      ((inSubgroup perfectResidual H ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)))
    Lc ∈ thetaComponentsAt 3 c ∧ 3 ∣ Nat.card Lc ∧
      ∀ K ∈ thetaComponentsAt 3 c, 3 ∣ Nat.card K → K = Lc

@[expose] def Item184_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    ∀ K ∈ scriptH A M, ∃ w ∈ Subgroup.normalizer (A : Set G),
      sectionCentralizer A (inSubgroup perfectResidual K)
          (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual K)) =
        ((Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom : Set G)

@[expose] def Item184_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    conjugatesIn (Subgroup.zpowers c) A = orbitIn (Subgroup.normalizer (A : Set G))
      (Subgroup.zpowers c)

@[expose] def Item184_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (A : Set G)) →
      (Subgroup.normalizer (A : Set G) ≤
          Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
        (IsE27 (omegaOneThree P) ∨ IsZ3TimesHeis (omegaOneThree P)) ∧
        c ∉ (frattini (omegaOneThree P)).map (omegaOneThree P).subtype) ∨
      (Subgroup.normalizer (A : Set G) ≤
          Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G) ∧
        (orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c)).ncard = 9 ∧
        A ≤ P ∧ (A.subgroupOf P).Characteristic ∧ HasSectionalThreeRankThree P)

@[expose] def Item184_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (A : Set G)) →
      CFSG.ABGLocalTools.IsSylowOf 3 P ⊤

@[expose] def Item185 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    A ⊓ inSubgroup perfectResidual H ≤ (Sec4.oTwoP 3 M).map M.subtype


@[expose] def Hyp187 {G : Type} [Group G] [Finite G] (A M H : Subgroup G) (c : G) : Prop :=
  H ∈ scriptHStar A M ∧ CFSG.Open.pCoreOf 2 H ≠ ⊥ ∧
    (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) ≠ ⊥ →
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
        Subgroup.normalizer (inSubgroup perfectResidual H : Set G))

@[expose] def Item187 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c →
      ∀ X ∈ invariantPiSubgroups ⊤ (A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M)) (piCompl 3),
        X ≤ Subgroup.normalizer (inSubgroup perfectResidual H : Set G)

@[expose] def Rem187 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    (∃ H₀ ∈ scriptH A M, CFSG.Open.pCoreOf 2 H₀ ≠ ⊥) →
      ∃ H : Subgroup G, ∃ c : G, Sec18H G A M H c ∧ Hyp187 A M H c

@[expose] def Item188 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    CFSG.ABGLocalTools.IsPConstrained 3 M →
      ∀ H ∈ scriptHStar A M, CFSG.Open.pCoreOf 2 H = ⊥

@[expose] def Item189 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c →
      let K := normalClosureIn M c
      let N := Subgroup.normalizer (inSubgroup perfectResidual H : Set G)
      (K ∈ oTwoComponentsIn M ∧ ¬ K ≤ N) ∧
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
      ((∃ n : ℕ, Odd n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n)) ∧
          IsMaxParabolicRankTwo (((K ⊓ N).subgroupOf K).map
            (QuotientGroup.mk' (CFSG.pCore 2 K)))) ∨
        (∃ n : ℕ, Even n ∧ 0 < n ∧
          Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 n)) ∧
          ¬ 4 ∣ (M ⊓ N).relIndex M))


end CFSG.RankThree.PartTwo.Sec18
