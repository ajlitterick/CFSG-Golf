module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4FinalBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Inv
public import CFSG.Sporadic.J4.QT2LocRadMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4HBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2B1
public import CFSG.Sporadic.J4.BasicFacts
public import Certificates.Certificate4011
public import Certificates.Certificate4015
public import Certificates.Certificate4116
import Certificates.Kernel.J4Q.ZB336Rad
import Certificates.Kernel.J4Q.ZFrAll
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZRows
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.C1GNInputs
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Sporadic.J4.QT2LocX0Main
public import CFSG.Sporadic.J4.QT2LocX0NMain
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Certificate43
import CFSG.Sporadic.J4.QT2LocFixMain
import CFSG.Sporadic.J4.QT2LocUniq

public section

namespace Certificates

open CertificateChecks

open CFSG.QuasithinUnique.A5

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 in
theorem certificate4112 : CFSG.Sporadic.J4.J4Basic → ClassRad B336a :=
  fun hF => classRad_b336 hF 37 zGwB336a (by decide) KernelJ4Q.chkZFr_A

end Certificates
