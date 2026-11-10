module

public import Certificates.Data.SmithD6RhoCheck

public noncomputable section

namespace CFSG.SmithD6

def uw7FLines (_ : Unit := ()) : Array Nat :=
  ((List.range 6).flatMap fun a => (List.range 6).filterMap fun b =>
    if a < b then some (lineOf (fV a) (fV b)) else none).toArray

def uw7LLines (_ : Unit := ()) : Array Nat :=
  ((List.range 6).flatMap fun a => (List.range 6).filterMap fun b =>
    if a != b then some (lineOf (eV a) (fV b)) else none).toArray

def uw7Gens (_ : Unit := ()) : Array Nat := uw7FLines () ++ uw7LLines ()


@[expose] def uw7Cls (j : Nat) : Nat :=
  if j == 0 then 0 else if adjW 0 j then 1 else if fB (wt 0) (wt j) then 3 else 2

def uw7Reps (_ : Unit := ()) : Array Nat :=
  (Array.range 4).map fun c => ((List.range 75735).find? fun j => uw7Cls j == c).getD 0

@[expose] def uw7Sizes : Array Nat := #[1, 1302, 41664, 32768]


@[expose] def uw7ChkGens (_ : Unit := ()) : Bool :=
  let gens := uw7Gens ()
  gens.size == 45 && gens.all fun g => decide (g < 365211) && planeImg g 0 == 0

@[expose] def uw7ChkCls (_ : Unit := ()) : Bool :=
  let reps := uw7Reps ()
  reps.size == 4 &&
    (List.range 4).all (fun c => decide (reps[c]! < 75735) && uw7Cls reps[c]! == c) &&
    (List.range 4).all fun c =>
      ((List.range 75735).filter fun j => uw7Cls j == c).length == uw7Sizes[c]!


@[expose] def uw7ChkDist (_ : Unit := ()) : Bool :=
  (List.range 75735).all fun j => uw7Cls j == distD 0 j

def uw7E0 (_ : Unit := ()) : Nat :=
  ((List.range 75735).find? fun j => fB (wt 0) (wt j) &&
    (List.range 6).all fun i => memR pbArr[j]! ppArr[j]! (eV i)).getD 0

@[expose] def uw7InB (e0 j : Nat) : Bool := fB (wt 0) (wt j) && j != e0

@[expose] def uw7BCls (e0 j : Nat) : Nat :=
  if fB (wt e0) (wt j) then 3 else if adjW e0 j then 1 else 2

def uw7BReps (_ : Unit := ()) : Array Nat :=
  let e0 := uw7E0 ()
  (Array.range 3).map fun c =>
    ((List.range 75735).find? fun j => uw7InB e0 j && uw7BCls e0 j == c + 1).getD 0

@[expose] def uw7BSizes : Array Nat := #[651, 18228, 13888]


@[expose] def uw7ChkE0 (_ : Unit := ()) : Bool :=
  let e0 := uw7E0 ()
  decide (e0 < 75735) && fB (wt 0) (wt e0) &&
    (List.range 6).all fun i => memR pbArr[e0]! ppArr[e0]! (eV i)

@[expose] def uw7ChkLevi (_ : Unit := ()) : Bool :=
  let e0 := uw7E0 ()
  let gens := uw7LLines ()
  gens.size == 30 &&
    gens.all fun g => decide (g < 365211) && planeImg g 0 == 0 && planeImg g e0 == e0

@[expose] def uw7ChkBCls (_ : Unit := ()) : Bool :=
  let e0 := uw7E0 ()
  let reps := uw7BReps ()
  reps.size == 3 &&
    (List.range 3).all (fun c => decide (reps[c]! < 75735) && uw7InB e0 reps[c]! &&
      uw7BCls e0 reps[c]! == c + 1) &&
    (List.range 3).all fun c =>
      ((List.range 75735).filter fun j => uw7InB e0 j && uw7BCls e0 j == c + 1).length ==
        uw7BSizes[c]!


end CFSG.SmithD6
