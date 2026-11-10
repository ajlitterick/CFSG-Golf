module

public import Certificates.Data.FzL26

public section

namespace Certificates.FzR10

open Certificates.FzL26

structure Par where
  e : Nat → Nat → Nat
  tI : Nat
  sI : Nat
  inTL : Nat → Bool
  inW : Nat → Bool
  inTZ : Nat → Bool
  rhoMap : Nat → Nat
  gens : Array Nat

@[expose] def elts : List Nat := List.range 512


@[expose] def kord (e : Nat → Nat → Nat) (x : Nat) : Nat :=
  if x = 0 then 1 else if e x x = 0 then 2 else
    if e (e x x) (e x x) = 0 then 4 else
      if e (e (e x x) (e x x)) (e (e x x) (e x x)) = 0 then 8 else 16


@[expose] def pfW (c : List Bool) (w : List Nat) : Bool :=
  w.foldl (fun a i => xor a c[i]!) false

@[expose] def validF (e : Nat → Nat → Nat) (gens : Array Nat) (wd : Array (List Nat))
    (c : List Bool) (A : List Nat) : Bool :=
  let f := wd.map (pfW c)
  A.all fun x => (List.range gens.size).all fun i =>
    f[e x gens[i]!]! == xor f[x]! c[i]!

@[expose] def vecsOf : Nat → List (List Bool)
  | 0 => [[]]
  | r + 1 => (vecsOf r).flatMap fun v => [false :: v, true :: v]


structure Data where
  wdT : Array (List Nat)
  gensS : Array Nat
  wdS : Array (List Nat)
  m1gens : List Bool → Array Nat
  m1wd : List Bool → Array (List Nat)

@[expose] def slist (P : Par) : List Nat := elts.filter fun x => P.e x P.tI == P.e P.tI x


@[expose] def m1 (P : Par) (D : Data) (c : List Bool) : List Nat :=
  (slist P).filter fun x => !(pfW c D.wdS[x]!)

@[expose] def vecS (P : Par) (D : Data) : List (List Bool) :=
  (vecsOf D.gensS.size).filter fun c =>
    validF P.e D.gensS D.wdS c (slist P) && !(pfW c D.wdS[P.tI]!)


@[expose] def vecH (P : Par) (D : Data) (c : List Bool) : List (List Bool) :=
  let A := m1 P D c
  let g := D.m1gens c
  let w := D.m1wd c
  (vecsOf g.size).filter fun c1 => validF P.e g w c1 A && !(pfW c1 w[P.tI]!)

@[expose] def hmk (P : Par) (D : Data) (c c1 : List Bool) : List Nat :=
  let w := D.m1wd c
  (m1 P D c).filter fun x => !(pfW c1 w[x]!)

@[expose] def hs (P : Par) (D : Data) : List (List Nat) :=
  (vecS P D).flatMap fun c => (vecH P D c).map fun c1 => hmk P D c c1


@[expose] def parOf (K : PCtx) (t : AutI) (act : Array Nat) : Par where
  e := K.em act
  tI := 64
  sI := 128
  inTL := fun x => t.ap (x % 64) == x % 64 && x / 64 % 4 == 0
  inW := fun x => t.ap (x % 64) == x % 64 && x / 64 < 2
  inTZ := fun x => x / 64 == 1 && x % 64 % 16 == 0
  rhoMap := fun x => rho0 (x % 64) + 64 * (x / 64)
  gens := #[1, 2, 4, 8, 64, 128, 256]

end Certificates.FzR10
