module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporCo
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporJ4
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporLy
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporMat
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporMcLHe
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporOrd
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporRuONHN
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporSuzTh
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.Mathieu.M22
public import CFSG.Certificates.CosetTableCompactPresented
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Sporadic.Bridge.J4SurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.McLSurj
public import CFSG.Sporadic.He
public import CFSG.Sporadic.J4.QTRankInvProof
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Presentation.HeExact
public import CFSG.Sporadic.Presentation.J4
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Presentation.M23
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Schreier.M23
import CFSG.Foundations
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem k150sTgt_a7 : K150sTgt (alternatingGroup (Fin 7)) :=
  ⟨alternatingGroup.isSimpleGroup (by simp),
    Or.inl KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1⟩

theorem k150sTgt_m22 : K150sTgt Blueprint.NativeSporadic.M22 :=
  ⟨CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2, Or.inr CFSG.Sporadic.Mathieu.card_M22⟩

section Six


theorem k150Six_of_tgt {J : Type} [Group J] (hJ : K150sTgt J) :
    ∀ s ∈ sporadics42, RowOfK150 J (Spor s) := by
  intro s hs
  simp only [sporadics42, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k150s_m11 hJ
  · exact k150s_m12 hJ
  · exact k150s_m22 hJ
  · exact k150s_m23 hJ
  · exact k150s_m24 hJ
  · exact k150s_j1 hJ
  · exact k150s_j2 hJ
  · exact k150s_j3 hJ
  · exact k150s_j4 hJ
  · exact k150s_mcl hJ
  · exact k150s_ly hJ
  · exact k150s_hs hJ
  · exact k150s_he hJ
  · exact k150s_suz hJ
  · exact k150s_ru hJ
  · exact k150s_on hJ
  · exact k150s_co3 hJ
  · exact k150s_co2 hJ
  · exact k150s_hn hJ
  · exact k150s_th hJ

theorem k150Six_a7 : ∀ s ∈ sporadics42, RowOfK150 (alternatingGroup (Fin 7)) (Spor s) :=
  k150Six_of_tgt k150sTgt_a7

theorem k150Six_m22 : ∀ s ∈ sporadics42, RowOfK150 Blueprint.NativeSporadic.M22 (Spor s) :=
  k150Six_of_tgt k150sTgt_m22

end Six

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
