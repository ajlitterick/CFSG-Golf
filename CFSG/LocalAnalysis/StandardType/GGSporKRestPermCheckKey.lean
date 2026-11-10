module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckMat

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv

@[expose] def keyOf {n : ℕ} (B : List ℕ) (x : Perm (Fin n)) : List ℕ :=
  B.map fun i => if h : i < n then (x ⟨i, h⟩).val else 0


end CFSG.StandardType.SporadicShape.PermCover
