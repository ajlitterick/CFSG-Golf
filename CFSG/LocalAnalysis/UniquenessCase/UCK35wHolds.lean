module

public import CFSG.LocalAnalysis.UniquenessCase.UCK35w
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableAlt
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRed
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRee
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeSolv
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOutPPrime
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven
public import CFSG.RankThree.PartTwo.Sec14.Item148Solvable
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section OfK35


end OfK35

section Holds


theorem k35w_holds
    : K35w := by
  intro G _ _ hX p hp hp2 M hM h2 hO
  by_cases hp3 : p = 3
  · subst hp3
    exact Or.inl (CFSG.RankThree.PartTwo.Sec14.isPSolvable_of_isSolvable Nat.prime_three
      (PartOne.Section7.isSolvable_of_isStronglyPEmbedded_three
        CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds hX hO h2 hM))
  · have hp5 : 5 ≤ p := by
      have h2' := hp.two_le
      by_contra h
      interval_cases p <;> simp_all (config := { decide := true })
    rcases PartOne.Section7.isSolvable_or_opp_alt_or_fi22_of_kFacts kFactSmallIdent_holds
        kFactOneLieTorus_holds stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
        (CFSG.AGLEmbedding.kFactSmallOutPPrime_of_smallIdent kFactSmallIdent_holds)
        CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv hp hp5 hX hO h2 hM with
      hs | hA | hF
    · exact Or.inl (CFSG.RankThree.PartTwo.Sec14.isPSolvable_of_isSolvable hp hs)
    · exact Or.inr (Or.inl hA)
    · exact Or.inr (Or.inr hF)

end Holds

end CFSG.LocalAnalysis.UniquenessCase.UCK
