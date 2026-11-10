module

public import Certificates.Data.CFSGNative.Schreier.Refine
public import Certificates.Data.CFSGNative.Co2Rank3.Orbits
public import Certificates.Data.CFSGNative.Co2Rank3.Data
public import CFSG.Sporadic.Co2Cert.Data

@[expose] public section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3.Native

set_option compiler.extract_closed false

@[expose] def co2DeltaList : List ℕ := co2Rec.stabilizerOrbits.getD 2 []

@[expose] def co2Nbr : Array (List ℕ) := adjSearch 2300 co2OrigArrs co2DeltaList

@[expose] def classCount (c : Array ℕ) (v : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin 2300 => c[w.val]! = c[v]!).card

@[expose] def labCount (lab : Array ℕ) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin 2300 => lab[w.val]! = r).card

@[expose] def commonCount (l₁ l₂ : List ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin 2300 => w.val ∈ l₁ ∧ w.val ∈ l₂).card

@[expose] def lev1Gens : Array (Array ℕ) := (level1Idx.map fun j => co2StrongArrs[j]!).toArray

@[expose] def lev2Gens : Array (Array ℕ) := (level2Idx.map fun j => co2StrongArrs[j]!).toArray

@[expose] def stabGens : Array (Array ℕ) :=
  (stabWords.map (wordA 2300 co2StrongArrs (rawInvs 2300 co2StrongArrs))).toArray

@[expose] def p0Rec : Array ℕ × Array ℕ × Array ℕ × Array ℕ := orbitSearch 2300 lev1Gens

@[expose] def stabRec : Array ℕ × Array ℕ × Array ℕ × Array ℕ := orbitSearch 2300 stabGens

@[expose] def p01Rec : Array ℕ × Array ℕ × Array ℕ × Array ℕ := orbitSearch 2300 lev2Gens

@[expose] def recOK (gens : Array (Array ℕ)) (rec : Array ℕ × Array ℕ × Array ℕ × Array ℕ)
    (roots : List (ℕ × ℕ)) : Bool :=
  orbitsOK 2300 gens rec.1 rec.2.1 rec.2.2.1 rec.2.2.2 && labelsOK 2300 rec.1 roots &&
    roots.all fun r => labCount rec.1 r.1 == r.2


end CFSG.Sporadic.Co2Rank3
