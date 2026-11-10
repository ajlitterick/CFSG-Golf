module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import Certificates.Data.O8p2NoDatum

public section

namespace CFSG.ClassicalInvolution.Q3.O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.ComponentClassification.J2Cover CFSG.ClassicalInvolution.O8Data

@[expose] def kGens (i : ℕ) : Array (Array ℕ) := ((centGens.getD i []).map omegaW).toArray

@[expose] def kS (i : ℕ) : Array (Array ℕ) := pushWords 360 (kGens i) (centDerived.getD i [])


end CFSG.ClassicalInvolution.Q3.O8
