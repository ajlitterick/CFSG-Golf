module

public import Certificates.Data.CFSGNative.Th.Certificate

public section

set_option compiler.extract_closed false

namespace CFSG.Sporadic.Th.Native

@[expose] def treeTable (n : Nat) (pl : Table) (gens : Nat → Table) (k : Nat) : Table :=
  if _h : 0 < k ∧ treePar (pl[k]!).toNat < k then
    compT n (gens (treeLab (pl[k]!).toNat)) (treeTable n pl gens (treePar (pl[k]!).toNat))
  else idT n
termination_by k

@[expose] def schreierTable (n : Nat) (pts pl pos : Table) (g1 g2 : Table) (k l : Nat) :
    Table × Bool :=
  let gl := letters g1 g2 l
  let j := ap pos (ap gl (ap pts k))
  let Rj := treeTable n pl (letters g1 g2) j
  let Rji := invT n Rj
  (compT n Rji (compT n gl (treeTable n pl (letters g1 g2) k)), invOK n Rj Rji)


@[expose] def hEval (t : Array (Nat × Nat)) (R X Y Xi Yi : Table) (k q : Nat) : Nat :=
  if _h : 0 < (t[k]!).1 ∧ (t[k]!).1 - 1 < k then
    ap (letters X Y (t[k]!).2)
      (hEval t R X Y Xi Yi ((t[k]!).1 - 1) (ap (letters Xi Yi (t[k]!).2) q))
  else ap R q
termination_by k

@[expose] def hFp (t : Array (Nat × Nat)) (R X Y Xi Yi : Table) (k : Nat) : Nat :=
  hEval t R X Y Xi Yi k 1 * 4294967296 + hEval t R X Y Xi Yi k 2

@[expose] def hFp2 (t₀ t₁ : Array (Nat × Nat)) (R₀ R₁ X Y Xi Yi : Table) (k : Nat) : Nat :=
  if k < t₀.size then hFp t₀ R₀ X Y Xi Yi k else hFp t₁ R₁ X Y Xi Yi (k - t₀.size)

@[expose] def hOrder (t₀ t₁ : Array (Nat × Nat)) (R₀ R₁ X Y Xi Yi : Table) : Array Nat :=
  let fps := (Array.range (t₀.size + t₁.size)).map (hFp2 t₀ t₁ R₀ R₁ X Y Xi Yi)
  (Array.range (t₀.size + t₁.size)).qsort fun i j => fps[i]! < fps[j]!


end CFSG.Sporadic.Th.Native
