module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSMatrices
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul

public section

namespace Certificates.ExcModel

open CFSG.StandardType.ZS

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) (ZMod 13)

structure M13 (n : ℕ) where
  val : Mat n

@[expose, noinline] def tabMat {n : ℕ} (T : List (List (ZMod 13))) : Mat n :=
  Matrix.of fun i j => (T.getD i []).getD j 0

@[expose] def strict {n : ℕ} (A : Mat n) : M13 n :=
  ⟨tabMat (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => A i j)⟩

@[expose] def r13 (x : ℕ) : ZMod 13 := (⟨x % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13)

@[expose] def fmul {n : ℕ} (A B : M13 n) : M13 n :=
  ⟨tabMat (List.ofFn fun i : Fin n => List.ofFn fun k : Fin n =>
    r13 (Fin.foldl n (fun (acc : ℕ) j => acc + (A.val i j).val * (B.val j k).val) 0))⟩


@[expose] def isOne {n : ℕ} (A : M13 n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    decide ((A.val i j).val = if i = j then 1 else 0)


@[expose] def a2 {n : ℕ} (a b : M13 n) : Bool :=
  let p := fmul a b
  !(isOne p) && isOne (fmul (fmul p p) p)


@[expose] def ctList (_ : Unit := ()) : List ((Fin 6 → ZMod 13) × (Fin 6 → ZMod 13)) :=
  ((List.finRange 6).flatMap fun i => (List.finRange 6).flatMap fun j =>
    if i < j then (List.range 3).map fun k =>
      (Pi.single i 1 - Pi.single j (om ^ k), Pi.single i 1 - Pi.single j (om ^ (2 * k)))
    else []) ++
  ([0, 1, 2].flatMap fun t1 => [0, 1, 2].flatMap fun t2 => [0, 1, 2].flatMap fun t3 =>
    [0, 1, 2].flatMap fun t4 => [0, 1, 2].flatMap fun t5 =>
      if (t1 + t2 + t3 + t4 + t5) % 3 = 0 then
        [((fun m : Fin 6 => om ^ (![0, t1, t2, t3, t4, t5] m)),
          (fun m : Fin 6 => om ^ (2 * ![0, t1, t2, t3, t4, t5] m)))]
      else [])


@[expose] def n4S (_ : Unit := ()) : List (M13 4) :=
  [strict (piMat 0 1 1), strict (piMat 1 2 1), strict (piMat 0 1 5), strict aMat]

@[expose] def en4S (_ : Unit := ()) : List (M13 4) :=
  n4S () ++ [strict (Matrix.diagonal fun i => if i = 3 then -1 else 1)]


end Certificates.ExcModel

end
