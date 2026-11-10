module

public import CFSG.Sporadic.Schreier.J4SElevenData
public import Certificates.Data.CFSGNative.J4.FixScan

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4.Native

@[expose] def natV2 (n : Nat) : V2 := V2.ofFn fun j => n.testBit j

@[expose] def pairRows (P : Array Nat × Array Nat) : Array V2 := P.1.map natV2


end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
