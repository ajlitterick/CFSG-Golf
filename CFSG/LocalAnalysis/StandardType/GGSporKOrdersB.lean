module

public import CFSG.RankThree.OddKernel.SporadicKernelRestrictionB
public import CFSG.Sporadic.Bridge.BBound
public import CFSG.Certificates.InvariantMerge
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.YGroups.DCE.B433Check

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Blueprint

theorem ggSporK_card_sporadicB :
    Nat.card (TauCeti.CFSGIndex.sporadic .B).Group = 4154781481226426191177580544000000 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  rw [← Nat.card_congr e.toEquiv]
  exact CFSG.RankThree.OddKernel.card_B_eq

end CFSG.StandardType.SporadicShape
