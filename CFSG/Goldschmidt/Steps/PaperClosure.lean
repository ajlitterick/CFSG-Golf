module

public import CFSG.Goldschmidt.OddCore
public import CFSG.Goldschmidt.StatementsG4
import CFSG.Goldschmidt.Steps.GAssembly
import CFSG.Goldschmidt.Steps.G4
import CFSG.Goldschmidt.Steps.G28
import CFSG.Goldschmidt.Steps.G210
import CFSG.Goldschmidt.Steps.G211
import CFSG.Goldschmidt.Steps.G312
import CFSG.Goldschmidt.Steps.GSz8Mult
import CFSG.Goldschmidt.Steps.G36
import CFSG.Goldschmidt.Steps.G3aBorel
import CFSG.Goldschmidt.Steps.G3NewPair
import CFSG.Goldschmidt.Steps.G51
import CFSG.Goldschmidt.Steps.G52
import CFSG.Goldschmidt.Steps.G53
import CFSG.Goldschmidt.Steps.G54
import CFSG.Goldschmidt.Steps.G55
import CFSG.Goldschmidt.Steps.G56
import CFSG.Goldschmidt.Steps.G61
import CFSG.Goldschmidt.Steps.G62
import CFSG.Goldschmidt.Steps.G63
import CFSG.Goldschmidt.Steps.G64
import CFSG.Goldschmidt.Steps.G71
import CFSG.Goldschmidt.Steps.G72
import CFSG.Goldschmidt.Steps.G73
import CFSG.Goldschmidt.Steps.G74
import CFSG.Goldschmidt.Steps.G75
import CFSG.Goldschmidt.Steps.G3aFStar
import CFSG.Goldschmidt.Steps.G38
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
import CFSG.Adapters.GeneralizedFitting
import CFSG.Walter.Bender1970.S1
import CFSG.Walter.Bender1970.S2
import CFSG.Walter.Bender1970.S3
import CFSG.Walter.Bender1970.S38
import CFSG.Walter.PSL2Facts

public section

namespace CFSG.Goldschmidt

theorem G64_of_steps
    (h37 : S_G37) (h311 : S_G311) : S_G64 :=
  have h55 := G55_of G31 h37 (G52_of h37) (G53_of h37) (G54_of G28 h37)
  have h51 := G51_of h55 (G56_of G31 h37 (G53_of h37) h55)
  have h62 := G62_of h311 h51 (G61_of G28) h37
  G64_of G31 (G38_of h37 G31) h51 (G61_of G28) h62 (G63_of h37 G312 h51 (G54_of G28 h37) h62)

theorem G71_of_steps
    (h37 : S_G37) (h311 : S_G311) : S_G71 :=
  G71_of G312 (G64_of_steps h37 h311) G31

theorem G74_of_steps
    (h37 : S_G37) (h311 : S_G311) : S_G74 :=
  have h71 := G71_of_steps h37 h311
  G74_of G31 (G36_of G32 GNewPair G31) h71 (G73_of G31 h37 h71)

theorem G75_of_steps
    (h37 : S_G37) (h311 : S_G311) : S_G75 :=
  G75_of (G74_of_steps h37 h311) (G36_of G32 GNewPair G31) G210 G211 GSz8Mult

theorem coreStatement_of_paperSteps
    (h37 : S_G37) (h311 : S_G311) (h76 : S_G76)
    (h89 : S_G89) : CoreStatement :=
  coreStatement_of_paper G4 (G72_of G4 (G71_of_steps h37 h311)) h76 h89

end CFSG.Goldschmidt
