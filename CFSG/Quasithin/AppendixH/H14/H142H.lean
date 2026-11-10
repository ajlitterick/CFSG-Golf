module

public import CFSG.Quasithin.AppendixH.H14.H142Card
public import CFSG.Quasithin.AppendixH.H14.H142HData
public import CFSG.Quasithin.AppendixH.H14.H142Group

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Open
open scoped Pointwise

@[expose] def stdMH : Subgroup S24 := M23g 8 ⊓ MulAction.stabilizer S24 stdH


theorem hGens_mem : ∀ a ∈ hGens, inAutOK a = true ∧ ∃ σ ∈ stdMH, HasArr σ a := by
  intro a ha
  obtain ⟨haut, h8, hperm⟩ := hGens_ok a ha
  refine ⟨haut, ?_⟩
  refine ⟨permOfArrD a, ?_, hasArr_permOfArrD haut⟩
  rw [stdMH, Subgroup.mem_inf]
  exact ⟨mem_M23g_of_arr (hasArr_permOfArrD haut) haut 8 h8,
    (MulAction.mem_stabilizer_iff).2 (smul_stdH_of_arr (hasArr_permOfArrD haut) h8 hperm)⟩

theorem hGens_permOfArrD_mem {a : Array ℕ} (ha : a ∈ hGens) : permOfArrD a ∈ stdMH := by
  obtain ⟨haut, σ, hσM, hσarr⟩ := hGens_mem a ha
  rw [hasArr_unique (hasArr_permOfArrD haut) hσarr]
  exact hσM


noncomputable def h3 : ↥stdMH :=
  ⟨permOfArrD hGens[1]!, hGens_permOfArrD_mem (by decide)⟩


end CFSG.Quasithin.AppendixH.H14
