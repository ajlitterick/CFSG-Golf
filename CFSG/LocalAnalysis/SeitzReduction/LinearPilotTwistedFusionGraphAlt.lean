module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionField

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (rootElt rootElt_of_ne coe_rootElt_of_ne
  rootElt_add rootElt_zero rootElt_mul_comm)
open FourGroupEvenCanonical UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog (blockSwapJ_transpose)
open CFSG.ComponentClassification.OutcomeLocal (blockSwapIsometryEquivStatedSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_linear_canonical_graph_symplectic_centralizers)

variable {K : Type} [Field K] {n r : ℕ}

section BlockSwap

theorem blockSwapJ_apply_eq_ite (hr : r + r = n) {p p' : Fin n}
    (hpp : (p' : ℕ) = p + r ∨ (p : ℕ) = p' + r) (u : Fin n) :
    (blockSwapJ n r : Matrix (Fin n) (Fin n) K) u p = if u = p' then 1 else 0 := by
  simp only [blockSwapJ, of_apply, Fin.ext_iff]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso
    omega
  · exfalso
    omega
  · rfl

theorem blockSwapJ_mul_single (hr : r + r = n) {p p' : Fin n}
    (hpp : (p' : ℕ) = p + r ∨ (p : ℕ) = p' + r) (q : Fin n) (c : K) :
    blockSwapJ n r * single p q c = single p' q c := by
  ext u v
  rw [mul_apply, Finset.sum_eq_single p]
  · rw [blockSwapJ_apply_eq_ite hr hpp, single_apply, single_apply]
    by_cases hu : u = p'
    · subst hu
      simp
    · have hu' : ¬p' = u := fun h => hu h.symm
      simp [hu, hu']
  · intro z _ hz
    rw [single_apply_of_row_ne (Ne.symm hz), mul_zero]
  · simp

theorem single_mul_blockSwapJ (hr : r + r = n) {p p' : Fin n}
    (hpp : (p' : ℕ) = p + r ∨ (p : ℕ) = p' + r) (q : Fin n) (c : K) :
    single q p c * blockSwapJ n r = single q p' c := by
  have h := congrArg transpose (blockSwapJ_mul_single (K := K) hr hpp q c)
  rwa [transpose_mul, blockSwapJ_transpose, transpose_single, transpose_single] at h

theorem blockSwapJ_mul_transvection_mul [CharP K 2] (hr : r + r = n) {i i' j j' : Fin n}
    (hi : (i' : ℕ) = i + r ∨ (i : ℕ) = i' + r) (hj : (j' : ℕ) = j + r ∨ (j : ℕ) = j' + r)
    (c : K) :
    blockSwapJ n r * transvection i j c * blockSwapJ n r = transvection i' j' c := by
  rw [transvection, transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    blockSwapJ_mul_self hr, blockSwapJ_mul_single hr hi, single_mul_blockSwapJ hr hj]

theorem transvection_transpose_eq_transvection (i j : Fin n) (c : K) :
    (transvection i j c)ᵀ = transvection j i c := by
  rw [transvection, transvection, transpose_add, transpose_one, transpose_single]


end BlockSwap


end CFSG.SeitzReduction.LinearPilot
