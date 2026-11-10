module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Check
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Facts
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThreeCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.SmallOddCore
open CFSG.RankThree.LocalRank

variable {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {pg pgInv : Array Table}
  {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool}

structure GroupDataSound (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) (pg : Array Table)
    (gg : ℕ → Equiv.Perm (Fin n)) (sift : Table → Bool) : Prop where
  lt : n < 2 ^ 32
  rep : ∀ l < pg.size, Rep n pg[l]! (gg l)
  gen : P = closure (gg '' {l | l < pg.size})
  sift : ∀ (T : Table) (g : Equiv.Perm (Fin n)), Rep n T g → sift T = true → g ∈ P


theorem GroupDataSound.mem (hD : GroupDataSound n P pg gg sift) {l : ℕ} (hl : l < pg.size) :
    gg l ∈ P := by
  rw [hD.gen]
  exact subset_closure ⟨l, hl, rfl⟩


end CFSG.AGLEmbeddingD2.Wilson.ThreeCore
