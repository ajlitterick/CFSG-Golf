module

public import CFSG.RankThree.PartOne.KLCE.Engine
public import CFSG.RankThree.PartOne.KLCE.FrameConj
public import CFSG.RankThree.PartOne.KLCE.Frob

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag)

open CFSG.Blueprint (LieModel)

open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne.KLCE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped MatrixGroups

section LayerData


@[expose] def OddJoin {M : Type} [Group M] (Γ P : Subgroup M) : Prop :=
  ∀ y ∈ Γ, ∃ m : ℕ, Odd m ∧ y ^ m ∈ P

theorem OddJoin.of_le {M : Type} [Group M] {Γ P : Subgroup M} (h : Γ ≤ P) : OddJoin Γ P :=
  fun y hy => ⟨1, odd_one, by simpa using h hy⟩

end LayerData

section Sector


end Sector

end CFSG.RankThree.PartOne.TCX.E
