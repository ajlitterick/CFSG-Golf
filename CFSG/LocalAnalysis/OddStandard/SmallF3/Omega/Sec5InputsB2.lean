module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartCoord
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.GH74.Defs
public import CFSG.Goldschmidt.BasicG
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
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
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.JRFacts
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def pairSet6 : Set (Fin 6 → ZMod 2) :=
  {v | vecWeight v = 1 ∨ vecWeight v = 2 ∨ vecWeight v = 5 ∨ vecWeight v = 6}

@[expose] def Asc82Fact59 : Prop :=
  ∀ g : (Fin 6 → ZMod 2) → (Fin 6 → ZMod 2), (∀ v w, g (v + w) = g v + g w) →
    (∀ v, v ∈ pairSet6 ↔ g v ∈ pairSet6) →
      ∃ σ : Equiv.Perm (Fin 8),
        ∀ w : Fin 8 → ZMod 2, IsEvenVec w → g (heartCoord w) = heartCoord (permVec σ w)

@[expose] def Asc82Fact510 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A : Subgroup G),
    Sec5RCtx G t L S z r B A → Set.ncard (conjClassIn (normalizer (A : Set G)) t) ≠ 7

end CFSG.OddStandard.SmallF3.Omega
