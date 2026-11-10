
module

public import Certificates.Data.Kernel.L5.Sh0T
public import CFSG.GH74.GLS.C3.Layer2.L5C9Inputs

public section

namespace CFSG.Certificates.Kernel.L5H

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5S
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.GH74.GLS.C3.Layer2.Model

@[expose] noncomputable def yC : CV 16 := cOf yHat

@[expose] noncomputable def wC : CV 16 := cOf wHat

@[expose] noncomputable def cHC : CV 16 := cOf cHat

@[expose] noncomputable def twC : CV 16 := cOf twPerm

@[expose] noncomputable def n24C : List (CV 16) := n24L.map cOf

@[expose] noncomputable def G72gC : List (CV 16) := [yC, wC, n24C.getD 6 1, cHC]

@[expose] noncomputable def G72C : List (CV 16) := closureList G72gC 8


@[expose] def pN (V : Finset (Fin 16)) : Nat :=
  (List.finRange 16).foldl (fun acc i => acc ||| if i ∈ V then 2 ^ i.val else 0) 0

@[expose] noncomputable def imgN (g : CV 16) (M : Nat) : Nat :=
  (List.range 16).foldl (fun acc i => acc ||| (M >>> i) % 2 * 2 ^ img 16 g.1 i) 0


@[expose] def fam0L : List (Finset (Fin 16)) := [{0, 5, 11, 14}, {0, 7, 10, 13}, {0, 1, 2, 3}, {0, 6, 9, 15}]

@[expose] def fam1L : List (Finset (Fin 16)) := [{0, 6, 11, 13}, {0, 7, 9, 14}, {0, 5, 10, 15}, {0, 1, 2, 3}]


@[expose] noncomputable def n24CovC (C : List (CV 16)) (tw : Bool) : Bool :=
  n24C.all fun a => decide ((if tw then twC * a * twC⁻¹ else a) ∈ C)

@[expose] def stepG (n : Nat) (mul : Nat → Nat → Nat) (gs : List Nat) (M : Nat) : Nat :=
  (List.range n).foldl (fun acc a =>
    acc ||| if M.testBit a then gs.foldl (fun acc' s => acc' ||| 2 ^ mul a s) 0 else 0) M

@[expose] def closG (n : Nat) (mul : Nat → Nat → Nat) (i1 : Nat) (gs : List Nat) (k : Nat) : Nat :=
  (stepG n mul gs)^[k] (2 ^ i1)

@[expose] noncomputable def mulGP : Nat :=
  pack 7 ((List.range 72).flatMap fun a => (List.range 72).map fun b =>
    G72C.idxOf (G72C.getD a 1 * G72C.getD b 1))

@[expose] noncomputable def mG (a b : Nat) : Nat := fld 7 mulGP (a * 72 + b)


end CFSG.Certificates.Kernel.L5H

end
