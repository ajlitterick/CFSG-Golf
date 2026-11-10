module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
public import CFSG.ClassicalInvolution.Generic.LineModelLinear

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ClassicalInvolution.Phan (blockMat)
open scoped MatrixGroups

section Commuting

variable {K : Type} [Field K] {n : ℕ}

theorem commutes_Lc_of_disjoint (h2 : (2 : K) ≠ 0) {T T' : Pair n} (hd : Disjoint T.1 T'.1) :
    Commutes (Lc K T) (Lc K T') := by
  intro x hx y hy
  refine mul_comm_of_inf_eq_bot h2 (zMat_mul_self T.1) (zMat_mul_self T'.1)
    (zMat_mul_comm _ _) ?_ hx hy
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, mem_eigSpace_zMat_neg_one h2, mem_eigSpace_zMat_neg_one h2] at hv
  rw [Submodule.mem_bot]
  funext a
  by_cases ha : a ∈ T.1
  · exact hv.2 a (Finset.disjoint_left.mp hd ha)
  · exact hv.1 a ha

theorem not_commutes_Lc_overlap (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {i j k : Fin n} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ Commutes (Lc K (⟨{i, j}, Finset.card_pair hij⟩ : Pair n))
      (Lc K (⟨{j, k}, Finset.card_pair hjk⟩ : Pair n)) := by
  intro hc
  let T : Pair n := ⟨{i, j}, Finset.card_pair hij⟩
  let T' : Pair n := ⟨{j, k}, Finset.card_pair hjk⟩
  have hne : zElt K T ≠ zElt K T' := by
    intro h
    have := congrArg Subtype.val (zElt_injective h2 h)
    have hi : i ∈ T.1 := by simp [T]
    rw [this] at hi
    simp only [T', Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · exact hij h
    · exact hik h
  have hcomm : Commute (zElt K T) (zElt K T') :=
    signGroup_comm (zElt_mem_signGroup T) (zElt_mem_signGroup T')
  have hL := isLongRootSL2_Lc h2 (by omega : 2 ≤ n) T
  have hL' := isLongRootSL2_Lc h2 (by omega : 2 ≤ n) T'
  rcases lemma_6_5 h2 hn hL hL' hcomm hne with ⟨-, -, -, hV⟩ | ⟨hnot, -⟩
  · have hv : (Pi.single j 1 : Fin n → K) ∈ minusSpace (zElt K T) ⊓ minusSpace (zElt K T') :=
      ⟨single_mem_eigSpace_zMat h2 (by simp [T]) 1, single_mem_eigSpace_zMat h2 (by simp [T']) 1⟩
    rw [hV, Submodule.mem_bot] at hv
    have := congr_fun hv j
    simp at this
  · exact hnot (Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx _ hL'.mem)


end Commuting

section A2

variable {K : Type} [Field K] {n : ℕ}

@[expose] def chart3 (hn : 3 ≤ n) (g : SL(n, K)) : SL(3, K) →* SL(n, K) :=
  (MulAut.conj g).toMonoidHom.comp (blockSL K n 3 0 (by omega))


end A2

section FrameProperties


end FrameProperties

end CFSG.ClassicalInvolution.Models
