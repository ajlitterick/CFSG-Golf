module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.RankOne
public import CFSG.Blueprint.Catalog
import CFSG.Goldschmidt.Steps.G3aBorel
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsH
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.Walter.Bender1970.S3.Setup
import CFSG.Walter.JRFacts

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint

theorem radRigid_of_fusionIsBenderGroup {X : Type} [Group X] [Finite X]
    (hs : IsSimpleGroup X) (hBT : HoldsTits X 2) (hX : fusionIsBenderGroup X) : RadRigid 2 X :=
  radRigid_of_stronglyEmbedded hs (fun T => by
    obtain ⟨D, h⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hX T
    exact ⟨h.se, h.card⟩) hBT

theorem radRigid_of_suzukiModel {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hBT : HoldsTits S 2) {f : ℕ} (h : SuzukiModel S 2 f) :
    RadRigid 2 S := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  refine radRigid_of_fusionIsBenderGroup hs hBT (Or.inr (Or.inr ⟨a, ha, ⟨?_⟩⟩))
  exact (e.trans (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)).trans
    (MulEquiv.subgroupCongr ((CFSG.Models.benderSzModel_eq_sz a).symm.trans
      (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a))).symm

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
