module

public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGHalfJoinSigned
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrKernel
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBMain

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResCentBoundNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime], ∀ hy : y ∈ Bs,
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
        MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)

@[expose] def GGTBTorNonsingularCov (p : ℕ) (lab : CFSG.Assembly.LargeEvenLabel) : Prop :=
  ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
    GGTBTorRowAt p lab r m N C M ∧ ¬ (p : ℤ) ∣ C.det


@[expose] def GGTBTorSplitLinearCov (p : ℕ) (lab : CFSG.Assembly.LargeEvenLabel) : Prop :=
  GGTBTorCov p lab ∧ lab.tag = .A ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGResCentBoundNbrRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime], ∀ hy : y ∈ Bs,
    (¬ GGInnerDiagOnLabel GGTBTorCov p Bs K) →
    (¬ GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K) →
    (¬ GGInnerDiagOnLabel GGF4ThreeLabel p Bs K) →
    (¬ GGInnerDiagOnLabel GGTwE6BadLabel p Bs K) →
    (p = 3 → ¬ GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel p Bs K) →
    (¬ GGInnerDiagOnLabel GGE6TwoThreeLabel p Bs K) →
    (p = 3 → ¬ GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs K) →
    (p = 7 → ¬ GGInnerDiagOnLabel
      (fun _ lab => lab = ⟨.A,8,1⟩ ∨ lab = ⟨.A,11,1⟩ ∨ lab = ⟨.E6,0,1⟩ ∨
        lab = ⟨.twE6,0,1⟩ ∨ lab = ⟨.E8,0,1⟩) p Bs K) →
    (¬ GGInnerDiagOnLabel
      (fun p lab => GGTableBNbrInnerNineSmallLabel p lab ∨ lab.tag = .triD4 ∨ lab.tag = .twF4)
      p Bs K) →
    (¬ GGInnerDiagOnLabel GGTableBNbrInnerNineClassicalLabel p Bs K) →
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
        MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)


end CFSG.StandardType
