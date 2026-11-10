module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.GH74.QTGen4.Finite4
public import CFSG.GH74.QTGen4.U42.PairExt
public import CFSG.GH74.QTGen4.U42.U0Core
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement


@[expose] def LeafL34DC : Prop :=
  ∀ (Mdl : L34Model) (hMdl : L34ModelFacts Mdl),
    ∀ (σ : MulAut ↥(Mdl.M1 ⊓ Mdl.M2)), (∀ b : ↥(Mdl.M1 ⊓ Mdl.M2), (b : Mdl.Y) ∈ pCoreOf 2 Mdl.M1 ↔
        ((σ b : ↥(Mdl.M1 ⊓ Mdl.M2)) : Mdl.Y) ∈ pCoreOf 2 Mdl.M1) →
      ∃ (a₁ : MulAut ↥Mdl.M1) (a₂ : MulAut ↥Mdl.M2),
        (∀ m : ↥Mdl.M1, (m : Mdl.Y) ∈ Mdl.M2 ↔ ((a₁ m : ↥Mdl.M1) : Mdl.Y) ∈ Mdl.M2) ∧
        (∀ m : ↥Mdl.M2, (m : Mdl.Y) ∈ Mdl.M1 ↔ ((a₂ m : ↥Mdl.M2) : Mdl.Y) ∈ Mdl.M1) ∧
        ∀ (b : ↥(Mdl.M1 ⊓ Mdl.M2)) (m₁ : ↥Mdl.M1) (m₂ : ↥Mdl.M2), (m₁ : Mdl.Y) = b →
          ((a₁ m₁ : ↥Mdl.M1) : Mdl.Y) = (m₂ : Mdl.Y) →
            ((a₂ m₂ : ↥Mdl.M2) : Mdl.Y) = ((σ b : ↥(Mdl.M1 ⊓ Mdl.M2)) : Mdl.Y)

@[expose] def LeafL34Glue : Prop :=
  ∀ (Mdl : L34Model) (hMdl : L34ModelFacts Mdl) {G : Type} [Group G] [Finite G] {P1 P2 S Q1 Q2 : Subgroup G} (ψ₁ : ↥P1 ≃* ↥Mdl.M1) (ψ₂ : ↥P2 ≃* ↥Mdl.M2),
    (S ≤ P1) →
    (S ≤ P2) →
    (Q1 ≤ S) →
    (Q2 ≤ P2) →
    (IsElemAbelian 2 Q1) →
    (Nat.card Q1 = 16) →
    (Q1 ≠ Q2) →
    (∀ x : ↥P1, (x : G) ∈ S ↔ (ψ₁ x : Mdl.Y) ∈ Mdl.T0) →
    (∀ x : ↥P2, (x : G) ∈ S ↔ (ψ₂ x : Mdl.Y) ∈ Mdl.T0) →
    (∀ x : ↥P1, (x : G) ∈ P2 ↔ (ψ₁ x : Mdl.Y) ∈ Mdl.M2) →
    (∀ x : ↥P2, (x : G) ∈ P1 ↔ (ψ₂ x : Mdl.Y) ∈ Mdl.M1) →
    (∀ x : ↥P1, (x : G) ∈ Q1 ↔ (ψ₁ x : Mdl.Y) ∈ pCoreOf 2 Mdl.M1) →
    (∀ x : ↥P2, (x : G) ∈ Q2 ↔ (ψ₂ x : Mdl.Y) ∈ pCoreOf 2 Mdl.M2) →
    Nonempty ((RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups Mdl.M1 Mdl.M2))


end CFSG.GH74.QTGen4.DSGen4
