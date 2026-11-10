module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.I22Check
public import CFSG.Sporadic.Recognition.M22MultiplierInputs

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Recognition.M22Multiplier CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.LieType.Multipliers CFSG.QuasithinUnique.Ch1.M22Cover
open CFSG.Monster.B CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 (rep_compA rep_idA eqA_iff eq_of_eqA)
open CFSG.Sporadic.Bridge.TwoGen.Native (relCheck wordTab letterTab)
open CFSG.Sporadic.Schreier.Tits (getElem!_ofFn_of_lt)

@[expose] def i22fParse (s : String) : Table :=
  (((s.splitOn " ").filterMap String.toNat?).map UInt32.ofNat).toArray

@[expose] def i22fAlphaText : String := include_str "I22FourAlpha.txt"

@[expose] def i22fBetaText : String := include_str "I22FourBeta.txt"

@[expose] def i22fN : ℕ := 32256

@[expose] def i22fAlpha (_ : Unit := ()) : Table := i22fParse i22fAlphaText

@[expose] def i22fBeta (_ : Unit := ()) : Table := i22fParse i22fBetaText

@[expose] def i22fPermOK (n : ℕ) (P R : Table) : Bool :=
  allIn 0 n (fun i => decide (ap P i < n) && decide (ap R i < n)) && invOK n P R && invOK n R P

@[expose] def i22fProd (n : ℕ) (gen : ℕ → Table) (w : List ℕ) : Table :=
  w.foldr (fun l T => compT n (gen l) T) (idT n)

@[expose] def i22fVertexTabs (n : ℕ) (tA tB : Table) : Array Table :=
  let gen : ℕ → Table := fun l => if l = 0 then tA else tB
  let tx : Array Table := Array.ofFn (n := 3) fun i => i22fProd n gen (covData.xwOf i)
  Array.ofFn (n := covData.nV) fun v => i22fProd n (fun l => tx[l % 3]!) (covData.words[v]!)

@[expose] def i22fIsInv (ea : Array (Array ℕ)) (v : ℕ) : Bool :=
  !eqA 22 ea[v]! (idA 22) && eqA 22 (compA 22 ea[v]! ea[v]!) (idA 22)

@[expose] def i22fPartner (n : ℕ) (ea : Array (Array ℕ)) (tv : Array Table) (v w : ℕ) : Bool :=
  w != v && eqA 22 (compA 22 ea[v]! ea[w]!) (compA 22 ea[w]! ea[v]!) &&
    compT n tv[v]! tv[w]! == compT n tv[w]! tv[v]!

@[expose] def i22fCount (n : ℕ) (tA tB : Table) : Bool :=
  let tv := i22fVertexTabs n tA tB
  let ea := covData.elaTab
  let invs := (List.range covData.nV).filter (i22fIsInv ea)
  decide ((invs.filter fun v => 14 ≤ (invs.filter (i22fPartner n ea tv v)).length).length ≤ 14)

@[expose] def i22fCheckT (n : ℕ) (α β : Table) : Bool :=
  let αi := invT n α
  let βi := invT n β
  i22fPermOK n α αi && i22fPermOK n β βi &&
    relCheck n α αi β βi ((coverWords m22Rels m22CommWord).map natWord) &&
    i22fCount n (wordTab n α αi β βi (natWord m22SurjA)) (wordTab n α αi β βi (natWord m22SurjB))

@[expose] def i22fCheck (_ : Unit := ()) : Bool :=
  decide (covData.nV = 128) && goodCheck covData covData.elaTab &&
    i22fCheckT i22fN (i22fAlpha ()) (i22fBeta ())

section Sound


end Sound


end CFSG.EvenSporadicStandard.M22Std
