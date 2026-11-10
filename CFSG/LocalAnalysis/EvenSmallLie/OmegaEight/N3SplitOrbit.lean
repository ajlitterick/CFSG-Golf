module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitNative
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitConj

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.UnitarySix.YamadaPar


section Orbits

variable {A : Array ℕ} {gs : Array (ℕ × ℕ)} (P : ℕ → Prop)


variable {P}


end Orbits


variable {gs : Array (ℕ × ℕ)} {E : Enum}


theorem conj_mem_of_relIndex_two {M S : Subgroup GL12} (hMS : M ≤ S) (h : M.relIndex S = 2)
    {y m : GL12} (hy : y ∈ S) (hm : m ∈ M) : y * m * y⁻¹ ∈ M := by
  have hn := Subgroup.normal_of_index_eq_two (H := M.subgroupOf S) h
  have := hn.conj_mem ⟨m, hMS hm⟩ (by rwa [mem_subgroupOf]) ⟨y, hy⟩
  rwa [mem_subgroupOf] at this


end CFSG.EvenSmallLie.OmegaEight.N3Split
