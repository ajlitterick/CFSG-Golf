module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KC.BSeed

open CFSG.KC

@[expose] noncomputable def low64 : Nat := nat_lit 18446744073709551615

@[expose] noncomputable def decChunkS (len : Nat) : Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ t => t)
    (fun _ ih N t => List.cons (Nat.land (Nat.shiftRight N (nat_lit 64)) (nat_lit 255))
      (ih (Nat.lor (Nat.shiftLeft (Nat.shiftRight N (nat_lit 72)) (nat_lit 64)) (Nat.land N low64)) t))
    len

@[expose] noncomputable def bytesOfS (L : List (Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun p _ ih => Prod.rec (motive := fun _ => List Nat) (fun N len => decChunkS len N ih) p) L

@[expose] noncomputable def decChunkSC (len : Nat) : Nat → List Char → List Char :=
  Nat.rec (motive := fun _ => Nat → List Char → List Char) (fun _ t => t)
    (fun _ ih N t => List.cons (Char.ofNat (Nat.land (Nat.shiftRight N (nat_lit 64)) (nat_lit 255)))
      (ih (Nat.lor (Nat.shiftLeft (Nat.shiftRight N (nat_lit 72)) (nat_lit 64)) (Nat.land N low64)) t))
    len

@[expose] noncomputable def charsOfS (L : List (Nat × Nat)) : List Char :=
  List.rec (motive := fun _ => List Char) List.nil
    (fun p _ ih => Prod.rec (motive := fun _ => List Char) (fun N len => decChunkSC len N ih) p) L

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def seedRun (d i1 : Nat) (R : Nat → Nat) (bs : List Nat) :
    Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun h i j _ => andB (Nat.beq h (nat_lit 0)) (andB (Nat.beq i i1) (Nat.beq j (nat_lit 0))))
    (fun c _ ih h i j r =>
      Bool.rec (motive := fun _ => Bool)
        (bIf(Nat.beq c (nat_lit 10), ih h i j r,
          bIf(Nat.ble (nat_lit 48) c, bIf(Nat.ble c (nat_lit 49),
            andB (Nat.blt i i1) (andB (Nat.beq (Nat.sub c (nat_lit 48)) (Nat.land r (nat_lit 1)))
              (strictB (Nat.succ j) (fun j' =>
                Bool.rec (motive := fun _ => Bool)
                  (strictB (Nat.shiftRight r (nat_lit 1)) (fun r' => ih h i j' r'))
                  (andB (Nat.beq (Nat.shiftRight r (nat_lit 1)) (nat_lit 0))
                    (strictB (Nat.succ i) (fun i' => ih h i' (nat_lit 0) (R i'))))
                  (Nat.beq j' d)))),
            false), false)))
        (bIf(Nat.beq c (nat_lit 10), ih (nat_lit 0) i j r, ih h i j r))
        (Nat.beq h (nat_lit 1)))
    bs

@[expose] noncomputable def seedChunkOK (d : Nat) (bs : List Nat) (hdr : Bool) (i0 i1 : Nat)
    (R : Nat → Nat) : Bool :=
  andB (Nat.ble i0 i1)
    (seedRun d i1 R bs (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) hdr) i0 (nat_lit 0) (R i0))

theorem decChunkSC_eq (len : Nat) : ∀ (N : Nat) (t : List Nat),
    decChunkSC len N (t.map Char.ofNat) = (decChunkS len N t).map Char.ofNat := by
  induction len with
  | zero => intro N t; rfl
  | succ len ih =>
    intro N t
    change List.cons _ (decChunkSC len _ _) = (List.cons _ (decChunkS len _ _)).map Char.ofNat
    rw [ih, List.map_cons]

theorem charsOfS_eq (L : List (Nat × Nat)) : charsOfS L = (bytesOfS L).map Char.ofNat := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨N, len⟩ := p
    change decChunkSC len N (charsOfS L) = (decChunkS len N (bytesOfS L)).map Char.ofNat
    rw [ih, decChunkSC_eq]

theorem decChunkS_append (len : Nat) : ∀ (N : Nat) (t u : List Nat),
    decChunkS len N t ++ u = decChunkS len N (t ++ u) := by
  induction len with
  | zero => intro N t u; rfl
  | succ len ih =>
    intro N t u
    change List.cons _ (decChunkS len _ _) ++ u = List.cons _ (decChunkS len _ _)
    rw [List.cons_append, ih]

theorem bytesOfS_append (L M : List (Nat × Nat)) : bytesOfS (L ++ M) = bytesOfS L ++ bytesOfS M := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨N, len⟩ := p
    change decChunkS len N (bytesOfS (L ++ M)) = decChunkS len N (bytesOfS L) ++ bytesOfS M
    rw [ih, decChunkS_append]

end CFSG.KC.BSeed

end
