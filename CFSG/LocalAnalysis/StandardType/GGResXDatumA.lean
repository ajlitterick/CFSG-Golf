module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupSymmetricFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreePerm
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResXDatumA {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) (n : ℕ) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (e : Fin n ≃ Λ),
    M = (CoxeterMatrix.A n).reindex e ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ)

theorem GGResXDatumA.card_automizer {G : Type} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] {Bs X : Subgroup G} (hD : GGResXDatumA p Bs X n) :
    Nat.card (ggAutomizer X Bs) = (n + 1).factorial := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM,
    _, _, _, _, _, ⟨f, _⟩, _⟩ := hD
  have hc : Nat.card (ggAutomizer X Bs) = Nat.card M.Group :=
    (Nat.card_congr f.toEquiv).symm
  rw [hM, Nat.card_congr ((CoxeterMatrix.A n).reindexGroupEquiv e).toEquiv] at hc
  obtain ⟨fP, _⟩ := ggCoxeterA_mulEquivPerm n
  rw [Nat.card_congr fP.toEquiv, Nat.card_perm, Nat.card_fin] at hc
  exact hc


end CFSG.StandardType
