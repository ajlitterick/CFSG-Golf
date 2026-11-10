module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBTorANarrow : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .A ∨ lab.tag = .twA) → 6 ≤ lab.rank → p ∣ lab.rank + 1 → p ∣ ggTorM lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
          (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I

@[expose] def GGTBTorLiftADepRows : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .A ∨ lab.tag = .twA) → 6 ≤ lab.rank → p ∣ lab.rank + 1 → p ∣ ggTorM lab →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank - 1 - ggTorEnn p lab) R

@[expose] def GGTBJTwoNodeLargeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGResXDatum p Bs L → GGResRowAt (fun p J X => ggRowTwoNode p J X ∧ 10 ≤ X.rank) p J L →
        GGResTwoNodeSideDatum p Bs L J) ∧
      (GGResXDatum p Bs K → GGResRowAt (fun p J X => ggRowTwoNode p J X ∧ 10 ≤ X.rank) p J K →
        GGResTwoNodeSideDatum p Bs K J)


end CFSG.StandardType

end
