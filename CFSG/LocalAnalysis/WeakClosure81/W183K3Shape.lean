module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.RankThree.PartTwo.Sec4.Census (tableOrder)

@[expose] def KShapeList (X : Type) [Group X] : Prop :=
  IsL2 X 2 ∨ IsU3 X 2 ∨ IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2 ∨
  (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 9 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e X) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((p % 4 = 3 ∧ LieModel X .PSL 3 p 1) ∨ (p % 4 = 1 ∧ LieModel X .PSU 3 p 1))) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel X .PSp 2 p 1)


end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
