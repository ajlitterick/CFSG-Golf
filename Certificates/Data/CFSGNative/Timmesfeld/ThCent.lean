module

public import Certificates.Data.CFSGNative.Th.Certificate

public section

set_option compiler.extract_closed false

namespace CFSG.Sporadic.Th.Native

@[expose] def wordRows (P Q : Array V4) (w : List Int) : Array V4 :=
  w.foldl (fun acc l => mulRows acc
    (if l = 1 ∨ l = -1 then P else if l = 2 then Q else mulRows Q Q)) idRows

@[expose] def powRowsN (M : Array V4) : Nat → Array V4
  | 0 => idRows
  | e + 1 => mulRows (powRowsN M e) M

@[expose] def abWord (s : String) : List Int := s.toList.map fun c => if c = 'a' then 1 else 2

@[expose] def x1Str : String :=
  "bbbbabbbbabbbbabbbbabbbbabbbbabbabbabbabbabbabbabbabbaaabababababababa\
    babbabbabbabbabbabb"

@[expose] def x2Str : String :=
  "bbabbabbabbabbabbbbabbbbabbbbabbbbabbbbabbbbabbbbabbbbabbbbabbbbabbbba\
    bbbbabbbbaababababbababbabbababababbababbabbababababbababbabbabbabbabb\
    abbabbabbabbabbabbabbabbabbabbababababab"

@[expose] def zRows (_ : Unit := ()) : Array V4 :=
  powRowsN (mulRows (wordRows (rowsOf seedA) (rowsOf seedB) (abWord x1Str))
    (wordRows (rowsOf seedA) (rowsOf seedB) (abWord x2Str))) 9

@[expose] def xRows (_ : Unit := ()) : Array V4 := wordRows (rowsOf seedA) (rowsOf seedB) xWord

@[expose] def yRows (_ : Unit := ()) : Array V4 := wordRows (rowsOf seedA) (rowsOf seedB) yWord

@[expose] def z0Rows (_ : Unit := ()) : Array V4 := wordRows (xRows ()) (yRows ()) zWord0

@[expose] def z1Rows (_ : Unit := ()) : Array V4 := wordRows (xRows ()) (yRows ()) zWord1

@[inline, expose] def imgIdx (st : BFSState) (t : Array V4) (i : Nat) : Nat :=
  (findSlot st.keys st.slots (imageKey t (readKey st.keys i))).2 - 1

@[expose] def matBlock (st : BFSState) (t : Array V4) (lo hi : Nat) : Table :=
  Array.ofFn (n := hi - lo) fun k => UInt32.ofNat (imgIdx st t (lo + k.val))

@[expose] def freshTable (t : Array V4) : Array V4 :=
  let z := (t[0]!).xor (t[0]!)
  t.map fun v => v.xor z

@[expose] def matTable (st : BFSState) (t : Array V4) (n c : Nat) : Table :=
  let b := n / (c + 1) + 1
  ((List.range (c + 1)).map fun j =>
    Task.spawn fun _ => matBlock st (freshTable t) (min n (j * b)) (min n ((j + 1) * b))).foldl
    (fun acc tk => acc ++ tk.get) #[]

@[expose] def matTableOK (st : BFSState) (t : Array V4) (T : Table) (n c : Nat) : Bool :=
  let b := n / (c + 1) + 1
  ((List.range (c + 1)).map fun j => Task.spawn fun _ =>
    let t' := freshTable t
    allIn (min n (j * b)) (min n ((j + 1) * b)) fun i =>
      decide (ap T i < n) && (readKey st.keys (ap T i)).beq (imageKey t' (readKey st.keys i))).all
    Task.get

@[expose] def applyTreeInv2 (pl P₁ P₂ : Table) (k : Nat) (q : Array Nat) : Array Nat :=
  if _h : 0 < k ∧ treePar (pl[k]!).toNat < k then
    if treeLab (pl[k]!).toNat = 1 then
      applyTreeInv2 pl P₁ P₂ (treePar (pl[k]!).toNat) (apT P₁ q)
    else
      applyTreeInv2 pl P₁ P₂ (treePar (pl[k]!).toNat) (apT P₂ q)
  else q
termination_by k

@[inline, expose] def stripZ (zT gpl alphaT betaInvT pl0 pos0 mxT myiT : Table) (p : Nat) :
    Nat × Array Nat :=
  let q := applyTreeInv2 gpl alphaT betaInvT p #[p, ap zT p, ap zT (ap zT p)]
  let k0 := ap pos0 q[1]!
  (k0, applyTreeInv2 pl0 mxT myiT k0 q)

@[inline, expose] def acceptAt (zT gpl alphaT betaInvT pl0 pos0 mxT myiT ptsW : Table) (m p : Nat) :
    Bool :=
  let r := stripZ zT gpl alphaT betaInvT pl0 pos0 mxT myiT p
  decide (r.1 < q0Size) && decide (findPt ptsW r.2[2]! < m)

@[expose] def countAcceptIn (zT gpl alphaT betaInvT pl0 pos0 mxT myiT ptsW : Table)
    (m lo hi : Nat) : Nat :=
  Nat.fold (hi - lo) (fun k _ acc =>
    if acceptAt zT gpl alphaT betaInvT pl0 pos0 mxT myiT ptsW m (lo + k) then acc + 1 else acc) 0

@[expose] def countAccept (zT gpl alphaT betaInvT pl0 pos0 mxT myiT ptsW : Table) (m n b : Nat) :
    Nat :=
  ((List.range ((n + b - 1) / b)).map fun j =>
    Task.spawn fun _ => countAcceptIn zT gpl alphaT betaInvT pl0 pos0 mxT myiT ptsW m (j * b)
      (min n ((j + 1) * b))).foldl (fun a t => a + t.get) 0

@[expose] def centChecks (st : BFSState) (n p0 bound c : Nat) (Z X Y Z0 Z1 : Array V4)
    (zT xT yT yiT z0T z1T alphaT betaInvT gpl : Table) (q0 : Table × Table × Table)
    (qw : Table × Table) : Bool :=
  let r := stripZ zT gpl alphaT betaInvT q0.2.1 q0.2.2 xT yiT p0
  let w := r.2[2]!
  matTableOK st (frTable (transposeRows Z)) zT n c &&
    matTableOK st (frTable (transposeRows X)) xT n c &&
    matTableOK st (frTable (transposeRows Y)) yT n c &&
    matTableOK st (frTable (transposeRows Z0)) z0T n c &&
    matTableOK st (frTable (transposeRows Z1)) z1T n c &&
    invOK n yT yiT &&
    treeOK n q0Size 1 q0.1 q0.2.1 (ap q0.2.2) xT yT &&
    decide (p0 < n) && decide (r.1 < q0Size) && r.2[0]! == 0 && r.2[1]! == 1 &&
    treeOK n q1Size w qw.1 qw.2 (findPt qw.1) z0T z1T &&
    decide (countAccept zT gpl alphaT betaInvT q0.2.1 q0.2.2 xT yiT qw.1 q1Size n 1048576 ≤ bound)

@[expose] def centCheck (p0 bound c : Nat) : Bool :=
  let st := thBFS ()
  let n := st.count
  let alphaT := tblOfBytes n st.alpha
  let betaT := tblOfBytes n st.beta
  let gpl := tblOfBytes n st.par
  let betaInvT := invT n betaT
  let Z := zRows ()
  let X := xRows ()
  let Y := yRows ()
  let Z0 := z0Rows ()
  let Z1 := z1Rows ()
  let zT := matTable st (frTable (transposeRows Z)) n c
  let xT := matTable st (frTable (transposeRows X)) n c
  let yT := matTable st (frTable (transposeRows Y)) n c
  let yiT := invT n yT
  let z0T := matTable st (frTable (transposeRows Z0)) n c
  let z1T := matTable st (frTable (transposeRows Z1)) n c
  let q0 := localBFS n 1 xT yT
  let r := stripZ zT gpl alphaT betaInvT q0.2.1 q0.2.2 xT yiT p0
  let qw := smallBFS r.2[2]! 60 z0T z1T
  centChecks st n p0 bound c Z X Y Z0 Z1 zT xT yT yiT z0T z1T alphaT betaInvT gpl q0 qw

end CFSG.Sporadic.Th.Native

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal


abbrev qN : Nat := 59049


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal
