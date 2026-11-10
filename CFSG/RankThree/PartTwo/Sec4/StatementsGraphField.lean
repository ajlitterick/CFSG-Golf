module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def IsHeisSLThreeFour (X : Type) [Group X] : Prop :=
  ∃ U V : Subgroup X, U ⊔ V = ⊤ ∧ (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) ∧ IsHeisThree U ∧
    Nonempty (V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
    Nat.card (U ⊓ V : Subgroup X) = 3

@[expose] def IsZ3L34OrHeisSL34 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) ∨ IsHeisSLThreeFour X


noncomputable abbrev starQuot (G : Type) [Group G] : G →* G ⧸ CFSG.pPrimeCore 3 G :=
  QuotientGroup.mk' (CFSG.pPrimeCore 3 G)

@[expose] def Concl434 {G : Type} [Group G] [Finite G] (A Q : Subgroup G) : Prop :=
  IsZ3L34OrHeisSL34 (A ⊔ layer G : Subgroup G) ∧ Nat.card Q = 2 ∧
    ∀ q ∈ Q, q ≠ 1 → InducesStdKind (layer G) q .graphField


@[expose] def Concl4442 {G : Type} [Group G] [Finite G] (A M H : Subgroup G) (s : G) : Prop :=
  s ∈ CFSG.Open.pCoreOf 2 (H ⊓ M) ∧ s ∈ Subgroup.centralizer (A : Set G) ∧
    InducesStdKind (inSubgroup perfectResidual H) s .graphField ∧
    ∃ hs : s ∈ H, ∃ X : Subgroup (H ⧸ CFSG.pCore 2 H), X.Normal ∧ IsZ3L34OrHeisSL34 X ∧
      X ⊔ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 H) (⟨s, hs⟩ : H)) = ⊤ ∧
      QuotientGroup.mk' (CFSG.pCore 2 H) (⟨s, hs⟩ : H) ∉ X

@[expose] def Item4_44_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M → ⊤ ∈ Late.scriptH₀ A M →
    ∃ s : G, Concl4442 A M ⊤ s

@[expose] def Concl4443 {G : Type} [Group G] [Finite G] (M H : Subgroup G) : Prop :=
  ∃ L ∈ oTwoComponents G, ¬ L ≤ M ∧
    (L = inSubgroup perfectResidual H ⊔ inSubgroup (CFSG.pCore 2) L ∨
      (Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
          projSL 3 (GaloisField 2 2)) ∧
        ∃ J ∈ oTwoComponents G, ⁅inSubgroup perfectResidual H, ⊤⁆ = L ⊔ J ∧
          Nonempty (L ⧸ CFSG.pCore 2 L ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
          ((∃ n : ℕ, 1 ≤ n ∧ Nonempty (J ⧸ CFSG.pCore 2 J ≃*
              Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * n)))) ∨
            IsExtOf (J ⧸ CFSG.pCore 2 J) Blueprint.NativeSporadic.M22 (Multiplicative (ZMod 3)))))


structure Ctx4443 (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G) : Prop where
  ctx444 : Ctx444 G A M
  mem_scriptH₀ : H ∈ Late.scriptH₀ A M
  concl4442 : Concl4442 A M H s


end CFSG.RankThree.PartTwo.Sec4
