module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProof

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

@[expose] def GGDependentReflectionDatum {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs L K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
    (ι : Additive ↥Bs ≃+ V) (φ : Option Λ → MulAut ↥Bs)
    (h : Option Λ → V) (α : Option Λ → Module.Dual (ZMod p) V) (b : Λ),
    (∀ node, α node (h node) = 2) ∧
      (∀ node, h node ≠ 0) ∧
      (∀ node vector, ggLin (p := p) ι (φ node) vector =
        vector - α node vector • h node) ∧
      ¬ LinearIndependent (ZMod p) h ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun node : Λ => φ (some node)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun node : {node : Λ // node ≠ b} => φ (some node)) ∪ {φ none})


@[expose] def GGCoxeterLabelResidualInputOn
    (label : ∀ (G : Type) [Group G] (p : ℕ) [Fact p.Prime],
      Subgroup G → Subgroup G → Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
      GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsOrWeyl' p B Bs x D J →
      ∀ [Fact p.Prime], ¬ GGCoxeterForkDatum p Bs L K →
      ¬ GGCoxeterStdDatum p Bs L K → label G p Bs L K →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)


end CFSG.StandardType
