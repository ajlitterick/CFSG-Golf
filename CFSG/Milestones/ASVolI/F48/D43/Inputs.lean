module

public import CFSG.Milestones.ASVolI.F48.D43.Data
public import CFSG.LieType.Ree.Mirror
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.ASVolI

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.ON.Native
open CFSG.Monster.B.Co2.Native (hexTable)
open CFSG.Blueprint.Chevalley

set_option compiler.extract_closed false

@[expose] def burnsideF48d_addC (a b : ℕ) : ℕ :=
  (a % 3 + b % 3) % 3 + 3 * ((a / 3 % 3 + b / 3 % 3) % 3) + 9 * ((a / 9 % 3 + b / 9 % 3) % 3)

@[expose] def burnsideF48d_mulC (a b : ℕ) : ℕ :=
  (a % 3 * (b % 3) + a / 3 % 3 * (b / 9 % 3) + a / 9 % 3 * (b / 3 % 3)) % 3 +
    3 * ((a % 3 * (b / 3 % 3) + a / 3 % 3 * (b % 3) + a / 3 % 3 * (b / 9 % 3) +
      a / 9 % 3 * (b / 3 % 3) + a / 9 % 3 * (b / 9 % 3)) % 3) +
    9 * ((a % 3 * (b / 9 % 3) + a / 3 % 3 * (b / 3 % 3) + a / 9 % 3 * (b % 3) +
      a / 9 % 3 * (b / 9 % 3)) % 3)

@[expose] def burnsideF48d_powC (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => burnsideF48d_mulC a (burnsideF48d_powC a k)

@[expose] def burnsideF48d_frobC (a : ℕ) : ℕ :=
  burnsideF48d_mulC a (burnsideF48d_mulC a a)

@[expose] def burnsideF48d_intC (z : ℤ) : ℕ := (z % 3).toNat

abbrev burnsideF48d_C : RootCertificate .D4 := Tag.rootCertificate .D4

@[expose] def burnsideF48d_idx (b : ℕ) : CFSG.LieType.Ree.Idx burnsideF48d_C :=
  if h : b < 4 then .inl ⟨b, h⟩ else
    if h' : b - 4 < burnsideF48d_C.roots.length then .inr ⟨b - 4, h'⟩ else .inl ⟨0, by decide⟩

@[expose] def burnsideF48d_ofIdx : CFSG.LieType.Ree.Idx burnsideF48d_C → ℕ
  | .inl j => j.val
  | .inr m => 4 + m.val

@[expose] def burnsideF48d_col (y : Bool) (i k b : ℕ) : Option (ℕ × ℤ) :=
  if hi : i < 4 then
    ((if y then CFSG.LieType.Ree.yCol burnsideF48d_C (Tag.stringData .D4) ⟨i, hi⟩ k
        (burnsideF48d_idx b)
      else CFSG.LieType.Ree.xCol burnsideF48d_C (Tag.stringData .D4) ⟨i, hi⟩ k
        (burnsideF48d_idx b))).map fun p => (burnsideF48d_ofIdx p.1, p.2)
  else none

@[expose] def burnsideF48d_colTab (_ : Unit := ()) :
    Array (Array (Array (Array (Option (ℕ × ℤ))))) :=
  #[false, true].map fun y => (Array.range 4).map fun i => (Array.range 4).map fun k =>
    (Array.range 28).map fun b => burnsideF48d_col y i k b

@[expose] def burnsideF48d_opStep (col : Option (ℕ × ℤ)) (cw : ℕ) (out : Array ℕ) : Array ℕ :=
  match col with
  | none => out
  | some (a, z) =>
    out.set! a (burnsideF48d_addC out[a]! (burnsideF48d_mulC cw (burnsideF48d_intC z)))

@[expose] def burnsideF48d_opCoord (T : Array (Array (Array (Array (Option (ℕ × ℤ))))))
    (y : Bool) (i c : ℕ) (w : Array ℕ) (out : Array ℕ) (b : ℕ) : Array ℕ :=
  if w[b]! = 0 then out else
    (List.range 4).foldl (fun out k =>
      burnsideF48d_opStep ((((T[if y then 1 else 0]!)[i]!)[k]!)[b]!)
        (burnsideF48d_mulC w[b]! (burnsideF48d_powC c k)) out) out

@[expose] def burnsideF48d_applyOp (T : Array (Array (Array (Array (Option (ℕ × ℤ))))))
    (y : Bool) (i c : ℕ) (w : Array ℕ) : Array ℕ :=
  (List.range 28).foldl (burnsideF48d_opCoord T y i c w) (Array.replicate 28 0)

@[expose] def burnsideF48d_unit (b : ℕ) : Array ℕ := (Array.replicate 28 0).set! b 1

@[expose] def burnsideF48d_genSpec (k : ℕ) : List (Bool × ℕ × ℕ) :=
  let c := if k = 2 ∨ k = 5 then 1 else if k = 3 ∨ k = 6 then 3 else 9
  let y := decide (5 ≤ k)
  if k = 0 then [(false, 2, 1)] else if k = 1 then [(true, 2, 1)] else
    [(y, 0, c), (y, 1, burnsideF48d_frobC c), (y, 3, burnsideF48d_frobC (burnsideF48d_frobC c))]

@[expose] def burnsideF48d_genCol (T : Array (Array (Array (Array (Option (ℕ × ℤ))))))
    (k b : ℕ) : Array ℕ :=
  (burnsideF48d_genSpec k).foldr (fun op w => burnsideF48d_applyOp T op.1 op.2.1 op.2.2 w)
    (burnsideF48d_unit b)

@[expose] def burnsideF48d_realW (w : Array ℕ) : W :=
  ofV (V.ofFn 154 fun q => if q < 84 then w[q / 3]! / 3 ^ (q % 3) % 3 else 0)

@[expose] def burnsideF48d_rowsOf (cols : Array (Array ℕ)) : Array W :=
  Array.ofFn (n := 154) fun q => if q.val < 84 then
    burnsideF48d_realW ((cols[q.val / 3]!).map
      (burnsideF48d_mulC (burnsideF48d_powC 3 (q.val % 3))))
    else W.zero

@[expose] def burnsideF48d_genRows (T : Array (Array (Array (Array (Option (ℕ × ℤ))))))
    (k : ℕ) : Array W :=
  burnsideF48d_rowsOf ((Array.range 28).map (burnsideF48d_genCol T k))

@[expose] def burnsideF48d_frobRows (_ : Unit := ()) : Array W :=
  Array.ofFn (n := 154) fun q => if q.val < 84 then
    burnsideF48d_realW ((burnsideF48d_unit (q.val / 3)).map fun x =>
      burnsideF48d_frobC (burnsideF48d_mulC (burnsideF48d_powC 3 (q.val % 3)) x))
    else W.zero


@[expose] def burnsideF48d_limbs (_ : Unit := ()) : Array ℕ :=
  hexTable 16 (4 * 26572) 0 burnsideF48d_KeysHex

@[expose] def burnsideF48d_keys (_ : Unit := ()) : Array W :=
  let t := burnsideF48d_limbs ()
  Array.ofFn (n := 53144) fun i =>
    let j := i.val / 2
    let w : W := ⟨UInt64.ofNat t[4 * j]!, UInt64.ofNat t[4 * j + 1]!, 0, 0,
      UInt64.ofNat t[4 * j + 2]!, UInt64.ofNat t[4 * j + 3]!, 0, 0⟩
    if i.val % 2 = 0 then w else w.neg


@[expose] def burnsideF48d_gen (k : ℕ) : Array ℕ :=
  hexTable 4 26572 (26572 * k) burnsideF48d_GensHex

@[expose] def burnsideF48d_phi (_ : Unit := ()) : Array ℕ :=
  hexTable 4 26572 0 burnsideF48d_PhiHex

@[expose] def burnsideF48d_toT (a : Array ℕ) : Table := a.map UInt32.ofNat

@[expose] def burnsideF48d_rows (T : Array (Array (Array (Array (Option (ℕ × ℤ)))))) (k : ℕ) :
    Array W :=
  if k = 8 then burnsideF48d_frobRows () else burnsideF48d_genRows T k


@[expose] def burnsideF48d_KW : List (List (Fin 17 × Bool)) :=
  (List.range 2).flatMap fun j => (List.range 26).map fun i =>
    List.replicate i ((2 : Fin 17), true) ++ List.replicate j ((3 : Fin 17), true)


end CFSG.ASVolI
