module

public import CFSG.LocalAnalysis.SectionRank.QTK.Interface
public import CFSG.RankThree.PartTwo.Census.Sporadic.RankThree46F2
public import CFSG.RankThree.PartTwo.Census.Sporadic.RankThree46Odd
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1
public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi22
public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi23
public import CFSG.RankThree.PartTwo.Census.Sporadic.B
public import CFSG.RankThree.PartTwo.Census.Sporadic.Klein
public import CFSG.RankThree.ThetaFree.Sporadic
public import CFSG.Sporadic.Bridge.Y443Split
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.CoxeterM

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartTwo.Census
open CFSG.QuasithinUnique.SQTK TauCeti.Sporadic

theorem y443_coxeter_pow (i j : Fin 12) :
    (PresentedGroup.of i * PresentedGroup.of j : Y443) ^ Monster.coxeterMatrix i j = 1 := by
  have key : ∀ i j : Fin 12, i ≠ j → (((i, j) ∈ Monster.edges ∨ (j, i) ∈ Monster.edges) ↔
      CFSG.Sporadic.Bridge.Y443.adjB i j = true) := by
    rw [Monster.edges_def]
    decide +kernel
  rw [Monster.coxeterMatrix_apply]
  split_ifs with hij hadj
  · subst hij
    rw [pow_one]
    exact CFSG.Sporadic.Bridge.Y443.x_mul_self _
  · exact CFSG.Sporadic.Bridge.Y443.x_adj hij
      ((CFSG.Sporadic.Bridge.Y443.adjacent_iff_adjB i j).2 ((key i j hij).1 hadj))
  · exact CFSG.Sporadic.Bridge.Y443.x_nadj hij fun h =>
      hadj ((key i j hij).2 ((CFSG.Sporadic.Bridge.Y443.adjacent_iff_adjB i j).1 h))

theorem four_le_localRank_three_of_mulEquiv_nativeM {G : Type} [Group G] [Finite G]
    (e : G ≃* NativeSporadic.M) (hG : ∃ g h : G, g * h ≠ h * g) : 4 ≤ localRank 3 G := by
  refine four_le_localRank_three_of_coxeter monsterEdges Monster.coxeterMatrix (fun i j => ?_)
    (Coxeter.edgeGraph_connected 0 (by decide +kernel) (by decide +kernel))
    (Coxeter.edgeGraph_cliqueFree_three (by decide +kernel))
    (PresentedGroup.of (rels := y443Relations)) (PresentedGroup.closure_range_of _)
    y443_coxeter_pow (K := commutator Y443) le_rfl e hG ![1, 3, 7, 10] ![0, 4, 8, 11]
    (by decide +kernel) (by decide +kernel) 5 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [Monster.coxeterMatrix_apply, Monster.edges_def]
  rfl


end CFSG.SectionRank.QTK
