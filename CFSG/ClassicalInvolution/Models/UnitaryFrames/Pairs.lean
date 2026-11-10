module

public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Frame
public import CFSG.ClassicalInvolution.Generic.LineModelUnitary
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

section CommutingU

theorem commutes_LcU_of_disjoint (h2 : (2 : K) ≠ 0) {T T' : Pair n} (hd : Disjoint T.1 T'.1) :
    Commutes (LcU K p f T) (LcU K p f T') := by
  intro x hx y hy
  refine mul_comm_of_inf_eq_bot_su h2 (i₁ := zEltU K p f T) (i₂ := zEltU K p f T')
    (zMat_mul_self T.1) (zMat_mul_self T'.1) (zMat_mul_comm _ _) ?_ hx hy
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  have h1 := (mem_eigSpace_zMat_neg_one h2).mp hv.1
  have h3 := (mem_eigSpace_zMat_neg_one h2).mp hv.2
  rw [Submodule.mem_bot]
  funext a
  by_cases ha : a ∈ T.1
  · exact h3 a (Finset.disjoint_left.mp hd ha)
  · exact h1 a ha

theorem not_commutes_LcU_overlap (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 3 ≤ n)
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ Commutes (LcU K p f (⟨{i, j}, Finset.card_pair hij⟩ : Pair n))
      (LcU K p f (⟨{j, k}, Finset.card_pair hjk⟩ : Pair n)) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  intro hc
  let T : Pair n := ⟨{i, j}, Finset.card_pair hij⟩
  let T' : Pair n := ⟨{j, k}, Finset.card_pair hjk⟩
  have hne : zEltU K p f T ≠ zEltU K p f T' := by
    intro h
    have := zMat_inj h2 (congrArg suMat h)
    have hi : i ∈ T.1 := by simp [T]
    rw [this] at hi
    simp only [T', Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · exact hij h
    · exact hik h
  have hcomm : Commute (zEltU K p f T) (zEltU K p f T') :=
    signGroupU_comm (zEltU_mem_signGroupU T) (zEltU_mem_signGroupU T')
  have hL := isLongRootSU2_LcU (p := p) (f := f) h2 (by omega : 2 ≤ n) T
  have hL' := isLongRootSU2_LcU (p := p) (f := f) h2 (by omega : 2 ≤ n) T'
  rcases lemma_6_5_su hK hp hn hL hL' hcomm hne with ⟨-, -, -, hV⟩ | ⟨hnot, -⟩
  · have hv : (Pi.single j 1 : Fin n → K) ∈
        minusSpaceSU (zEltU K p f T) ⊓ minusSpaceSU (zEltU K p f T') :=
      ⟨single_mem_eigSpace_zMat h2 (by simp [T]) 1, single_mem_eigSpace_zMat h2 (by simp [T']) 1⟩
    rw [hV, Submodule.mem_bot] at hv
    have := congr_fun hv j
    simp at this
  · exact hnot (Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx _ hL'.mem)


end CommutingU

section A2U


end A2U

section FramePropertiesU


end FramePropertiesU

end CFSG.ClassicalInvolution.Models
