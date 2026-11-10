module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Assembly
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.FourHX
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC

theorem tiStage1930_of_s23InputsUC (hE : UC22P20gExcFacts)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G)
    (h846 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      AGL81TheoremC G → ∀ S : Setup G, S.InMSigma →
        F08.R846 (PartTwo.Three.dataOfSetup hS S))
    (h899 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
        CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) →
          F08.R899 (PartTwo.Three.dataOfSetup hS S))
    (h : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      AGL81TheoremC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
        CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) →
          ∃ Ch : Choice2011 G, S23Inputs (PartTwo.Three.dataOfSetup hS S) Ch ∧
            S21_8N (PartTwo.Three.dataOfSetup hS S) Ch ∧
              S21_21B (PartTwo.Three.dataOfSetup hS S) Ch) :
    CFSG.Yardstones.Me2c15c2c995a.AscSectionTwentyThree := by
  intro G _ _ hS hUC S hMS h1930 hTI
  obtain ⟨Ch, I, h218, h2121⟩ := h G hS hUC (hC G hS) S hMS h1930 hTI
  exact false_of_s23Inputs hE hSch S.notCatalog (PartTwo.Three.dataOfSetup hS S) Ch
    h1930 (by simpa [PartTwo.Three.dataOfSetup] using (dataExt_ofSetup hS S).hne)
    hTI (UC6S846.sigmaStd_dataOfSetup hS S) (PartTwo.Three.r6_1_dataOfSetup hS S)
    (sigma23Std_ofSetup hS S) (uc22p22c_hyp612_of_sigma2 hS S)
    (UC6.r6_11Used_dataOfSetup hS S) (h846 G hS hUC (hC G hS) S hMS)
    (h899 G hS hUC S hMS h1930 hTI) h218 h2121 hS.rank I


end CFSG.LocalAnalysis.UniquenessCase.UC22
