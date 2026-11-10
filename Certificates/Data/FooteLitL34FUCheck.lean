module

public import Certificates.Data.GrSLitL34FactsRealBCheck

public section

namespace CFSG.ComponentClassification.TBLit.L34FU

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

@[expose] def pow4X (x : MElt) : MElt := mulM (mulM x x) (mulM x x)

@[expose] def orb4 : Array Tab := (orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₄T 1963).tabs

@[expose] def candTab (t i : ℕ) : Tab := comp 42 (wordTab (tg t)) (repTab i)

@[expose] def candOK (t i : ℕ) : Bool :=
  comp 42 (candTab t i) r₂T == comp 42 r₂T (candTab t i) &&
    comp 42 (candTab t i) (candTab t i) == idTab 42 && orb4.contains (candTab t i)


end CFSG.ComponentClassification.TBLit.L34FU
