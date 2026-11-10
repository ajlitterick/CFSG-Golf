module

public import CFSG.Milestones.ASVolI.H13

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH CFSG.Monster.Code
open scoped Pointwise

@[expose] def maskSetOf (m : ℕ) : Finset (Fin 24) :=
  Finset.univ.filter fun i => m.testBit i = true

theorem mem_maskSetOf (m : ℕ) (i : Fin 24) : i ∈ maskSetOf m ↔ m.testBit i = true := by
  simp [maskSetOf]

theorem smul_maskSetOf {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a) (m : ℕ) :
    σ • maskSetOf m = maskSetOf (permM a m) := by
  ext j
  rw [← Finset.inv_smul_mem_iff, Equiv.Perm.smul_def, mem_maskSetOf, mem_maskSetOf,
    ← bvec_ne_zero_iff, ← bvec_ne_zero_iff, ← permWord_bvec hσ]
  exact Iff.rfl


end CFSG.Quasithin.AppendixH.H14
