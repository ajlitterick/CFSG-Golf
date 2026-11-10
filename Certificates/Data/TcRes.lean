module

public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace Certificates.TcRes

set_option compiler.extract_closed false


structure TcrSys where
  rank : Nat
  cartan : Array Int
  roots : Array (List Int)
  ip : Array (Array Int)
  neg : Array Nat
  refl : Array (Array Nat)
  basis : Array Nat
  posFlag : Array Bool
  adj : Array (List Nat)
  par : Array (Nat × Nat)
  idx : Std.HashMap (List Int) Nat


inductive TcrKind
  | inner
  | suN
  | twoD
  | exc
  deriving DecidableEq


inductive TcrTg
  | A
  | twA
  | D
  | twD
  | E6
  | E7
  | E8
  | twE6
  | triD4
  deriving DecidableEq

structure TcrLab where
  t : TcrTg
  r : Nat
  n : Nat
  deriving DecidableEq

@[expose] def tcrComponentLabel (r N : Nat) (k : TcrKind) (n : Nat) : TcrLab :=
  match k with
  | .inner =>
    if N = r * (r + 1) then ⟨.A, r, n⟩
    else if N = 2 * r * (r - 1) then ⟨.D, r, n⟩
    else if r = 6 then ⟨.E6, 0, n⟩
    else if r = 7 then ⟨.E7, 0, n⟩
    else ⟨.E8, 0, n⟩
  | .suN => ⟨.twA, r, n⟩
  | .twoD => ⟨.twD, r, n⟩
  | .exc => if r = 6 then ⟨.twE6, 0, n⟩ else ⟨.triD4, 0, n⟩

@[expose] def tcrLabelClass (l : TcrLab) : List TcrLab :=
  l :: (match l.t with
    | .A => if l.r == 3 then [⟨.D, 3, l.n⟩]
        else if l.r == 1 && l.n % 2 == 0 then [⟨.twD, 2, l.n / 2⟩] else []
    | .D => if l.r == 3 then [⟨.A, 3, l.n⟩] else []
    | .twD => if l.r == 3 then [⟨.twA, 3, l.n⟩]
        else if l.r == 2 then [⟨.A, 1, 2 * l.n⟩] else []
    | .twA => if l.r == 3 then [⟨.twD, 3, l.n⟩] else []
    | _ => [])

@[expose] def tcrUntw (t : TcrTg) : Bool :=
  match t with
  | .A | .D | .E6 | .E7 | .E8 => true
  | _ => false

@[expose] def tcrSplitT (p : Nat) (l : TcrLab) : Bool :=
  (tcrUntw l.t && (2 ^ l.n - 1) % p == 0) ||
  (!tcrUntw l.t && l.t != .triD4 && (2 ^ l.n + 1) % p == 0) ||
  ((l.t == .twD || l.t == .triD4) && (2 ^ l.n - 1) % p == 0) ||
  (l.n == 1 && p == 3)

@[expose] def tcrHalfSplitT (p : Nat) (l : TcrLab) : Bool :=
  tcrSplitT p l ||
  ((l.t == .D || l.t == .E7 || l.t == .E8) && (2 ^ l.n + 1) % p == 0) ||
  (((l.t == .twA && l.r == 5) || l.t == .twE6) && (2 ^ l.n - 1) % p == 0) ||
  (l.t == .A && l.r == 5 && l.n == 2 && p == 5) ||
  (l.t == .A && l.r == 8 && l.n == 1 && p == 7) ||
  (l.t == .E6 && l.n == 1 && p == 7)


structure TcrCData where
  e : Nat
  r : Nat
  N : Nat
  ks : List TcrKind

instance : Inhabited TcrCData := ⟨⟨0, 0, 0, []⟩⟩


@[expose] def tcrLabsOf (d : TcrCData) (f : Nat) : List TcrLab :=
  d.ks.flatMap fun k => tcrLabelClass (tcrComponentLabel d.r d.N k (d.e * f))


@[expose] def tcrAllowedC1 (ε : Int) (f : Nat) (dJ dx : TcrCData) : Bool :=
  if ε == 1 && f == 1 then
    (dJ.r == 1 && dJ.N == 2 && dJ.e == 2 && dJ.ks == [.inner] &&
      ((dx.r == 2 && dx.N == 6 && dx.e == 2 && dx.ks == [.inner]) ||
       (dx.r == 4 && dx.N == 24 && dx.e == 1 && dx.ks == [.twoD]) ||
       (dx.r == 5 && dx.N == 30 && dx.e == 1 && dx.ks == [.inner]))) ||
    (dJ.r == 2 && dJ.N == 6 && dJ.e == 2 && dJ.ks == [.inner] &&
      dx.r == 5 && dx.N == 30 && dx.e == 1 && dx.ks == [.inner])
  else if ε == -1 && f == 1 then
    dJ.r == 1 && dJ.N == 2 && dJ.e == 3 && dJ.ks == [.inner] &&
      ((dx.r == 2 && dx.N == 6 && dx.e == 3 && dx.ks == [.suN]) ||
       (dx.r == 4 && dx.N == 24 && dx.e == 1 && dx.ks == [.exc]) ||
       (dx.r == 5 && dx.N == 30 && dx.e == 1 && dx.ks == [.suN]))
  else if ε == -1 && f == 2 then
    dJ.r == 1 && dJ.N == 2 && dJ.e == 2 && dJ.ks == [.inner] &&
      ((dx.r == 2 && dx.N == 6 && dx.e == 2 && dx.ks == [.inner]) ||
       (dx.r == 4 && dx.N == 24 && dx.e == 1 && dx.ks == [.twoD]))
  else false


@[expose] def tcrSplitFree (l : TcrLab) : Bool :=
  (tcrUntw l.t && l.n % 4 == 0) || (!tcrUntw l.t && l.t != .triD4 && l.n % 4 == 2) ||
  ((l.t == .twD || l.t == .triD4) && l.n % 4 == 0)

@[expose] def tcrHalfFree (l : TcrLab) : Bool :=
  tcrSplitFree l || ((l.t == .D || l.t == .E7 || l.t == .E8) && l.n % 4 == 2) ||
  (((l.t == .twA && l.r == 5) || l.t == .twE6) && l.n % 4 == 0)


end Certificates.TcRes

end
