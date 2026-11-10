module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23U52Points
public import CFSG.Sporadic.SmallOddCore.CentData
public import Certificates.Data.CFSGNative.Schreier.Check
public import Mathlib

public section

namespace CFSG.ComponentClassification.GSThmB.U52

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def codeA : ℕ := 1104008183840

@[expose] def codeB : ℕ := 1838666383372

@[expose] def matA : Matrix (Fin 5) (Fin 5) CFSG.Fischer.F4 := matN codeA

@[expose] def matB : Matrix (Fin 5) (Fin 5) CFSG.Fischer.F4 := matN codeB

@[expose] def tabA : Array ℕ := tabN codeA

@[expose] def tabB : Array ℕ := tabN codeB

@[expose] def chainS : Array (Array ℕ) := #[
    tabA, tabB, tabN 1021137073651713, tabN 70979213086723, tabN 844631096999939,
    tabN 844609806901251, tabN 281479288520705, tabN 281483583619073, tabN 844631138902019]

@[expose] def chainW : Array (List ℤ) := #[
    [], [], [-1, 2], [2, 1, 1], [-4, -3, -3, 4, 4, -3], [4, 5, -4], [6, 6, 6], [5, -6, 5, -6],
    [-7, -8, -5, -8, 7, -5]]

@[expose] def chainBase : List (Fin 341) := [0, 1, 16, 4, 64]

@[expose] def baseArr : Array ℕ := (chainBase.map Fin.val).toArray


end CFSG.ComponentClassification.GSThmB.U52
