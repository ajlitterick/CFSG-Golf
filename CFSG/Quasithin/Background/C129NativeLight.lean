module

public import CFSG.Quasithin.Background.C129NativeSet
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Closed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Holds
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.B4ModelsWitness
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.C1PackC129Solv
public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.SectionRank

namespace C129Native

theorem a38ForSQTKCat_proved
    : Vol2Native.A38ForSQTKCat :=
  Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact Vol2Native.a134SQTKFactCat
    Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved

theorem joinForm_of_minParabolicBlocks
    (hMB : MinParabolicBlocks)
    (hB113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat) (G : Type) [Group G] [Finite G] :
    JoinForm G := by
  intro X T M hX hSQ hT hT0 hcgs hMX
  have hTM : T ≤ M := fun t ht =>
    hcgs (inf_normalizer_le_cgsIn hT0 ⟨hT.1 ht, Subgroup.le_normalizer ht⟩)
  have h127 : L238.C127StatementCat (G := G) := L246C127.c127StatementCat_of_asB113 hB113
  have h123 : L238.C123TwoCgsStatement (G := G) := L246.C123.c123_holds G
  have hB42 : L238.AltBlockStatementJCat (G := G) := L238.altBlockStatementJCat_holds
  have hXq := Vol2Native.SQTKHypCat.quotient_pCore ↥X hSQ
  exact L238.lemma_C129_of_blocks h127 h123 hB42
    (L246A7.c129A7_of_inputs hMB h127 h123 hB42 a38ForSQTKCat_proved) hX hSQ
    (a38ForSQTKCat_proved _ hXq) (Vol2Native.a37ForSQTKCat_proved _ hXq) hT hT0 hcgs hMX
    (fun U hU hUM => L246A7.exists_block_of_mem_uFamHat_gen hMB hX hSQ hT hcgs hTM hU hUM)

end C129Native

theorem asc129StatementUsed_of_minParabolicBlocks
    (hMB : MinParabolicBlocks)
    (hB113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat) (G : Type) [Group G] [Finite G] :
    ASC129StatementUsed G := by
  have h127 : L238.C127StatementCat (G := G) := L246C127.c127StatementCat_of_asB113 hB113
  have h123 : L238.C123TwoCgsStatement (G := G) := L246.C123.c123_holds G
  have hB42 : L238.AltBlockStatementJCat (G := G) := L238.altBlockStatementJCat_holds
  exact C129Native.asc129StatementUsed_of_join (C129Native.joinForm_of_minParabolicBlocks hMB hB113 G)
    (L246A7.c129A7_of_inputs hMB h127 h123 hB42 C129Native.a38ForSQTKCat_proved)

end CFSG.Quasithin
