module

public import CFSG.RankThree.PartOne.TCX.E.AnFamily
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KLCE.A2Sector

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Matrix CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KLCE
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec)

open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped MatrixGroups Matrix

section Defs


@[expose] def e8A4Embedding (v : WeylGroup Tag.E8) : AnEmbedding Tag.E8 (2 + 3) (sigmaSetE8A4 v) where
  ρ L _ := rhoSigmaE8A4 L v
  r := sigmaRootE8A4 v
  mem _ := mem_sigmaSetE8A4_iff
  isRoot _ _ hij := isRoot_sigmaRootE8A4 v hij
  neg := sigmaRootE8A4_neg v
  inj _ _ := rhoSigmaE8A4_injective v
  range _ _ := rhoSigmaE8A4_range v
  gen _ _ i j hij := rhoSigmaE8A4_transvection v i j hij
  tor _ _ b := ⟨fun i => rootChar b (wbE8A4 v i), fun A => rhoSigmaE8A4_torus v b A⟩
  diag _ _ A hA := rhoSigmaE8A4_diagonal v A hA


end Defs

section Frame


end Frame

section Family


end Family

section Sectors


end Sectors

end CFSG.RankThree.PartOne.TCX.E
