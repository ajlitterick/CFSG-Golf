module

public import CFSG.Sporadic.Schreier.Co1EigenPlanes

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD)
open ElemThree Matrix

@[expose] noncomputable def planeAct
    (j : Fin 12) (x : E) : plane j →ₗ[ZMod 2] plane j :=
  (Matrix.mulVecLin ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))).restrict
    fun _ hv => E_mulVec_mem_plane x.2 hv

theorem planeAct_apply
    (j : Fin 12) (x : E) (v : plane j) :
    (planeAct j x v : Vec24) = ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ (v : Vec24) :=
  rfl

@[expose] noncomputable def planeRep
    (j : Fin 12) : Representation (ZMod 2) E (plane j) where
  toFun := planeAct j
  map_one' := by
    ext v
    rw [planeAct_apply, OneMemClass.coe_one, Units.val_one, one_mulVec]
    rfl
  map_mul' x y := by
    ext v
    rw [planeAct_apply, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
    rfl


theorem q_ne_zero
    (j : Fin 12) : q j ≠ 0 := by
  intro h
  have := linearIndependent_q.ne_zero (j, 0)
  simp only [Fin.val_zero, pow_zero, one_mulVec] at this
  exact this h

theorem linearIndependent_pair_of_ne {v w : Vec24} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) :
    LinearIndependent (ZMod 2) ![v, w] := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h i
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  have h01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have key : ∀ s t : ZMod 2, s • v + t • w = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    rcases h01 s with rfl | rfl <;> rcases h01 t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, one_smul, zero_add] at hst
      exact absurd hst hw
    · rw [zero_smul, one_smul, add_zero] at hst
      exact absurd hst hv
    · rw [one_smul, one_smul] at hst
      refine absurd ?_ hvw
      rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
      exact hst
  have h2 : (f 0 - g 0) • v + (f 1 - g 1) • w = 0 := by
    linear_combination (norm := module) h
  obtain ⟨h0, h1⟩ := key _ _ h2
  fin_cases i
  · exact sub_eq_zero.mp h0
  · exact sub_eq_zero.mp h1

theorem zM_mulVec_ne_zero
    {v : Vec24} (hv : v ≠ 0) : zM *ᵥ v ≠ 0 := by
  intro h
  apply hv
  rw [← one_mulVec v, ← zM_cube, pow_succ, ← mulVec_mulVec, h, mulVec_zero]

theorem finrank_plane
    (j : Fin 12) : Module.finrank (ZMod 2) (plane j) = 2 := by
  have hli : LinearIndependent (ZMod 2) ![q j, zM *ᵥ q j] :=
    linearIndependent_pair_of_ne (q_ne_zero j) (zM_mulVec_ne_zero (q_ne_zero j))
      (fun h => zM_mulVec_ne_self (q_ne_zero j) h.symm)
  have := finrank_span_eq_card hli
  rw [Fintype.card_fin] at this
  unfold plane
  rw [show ({q j, zM *ᵥ q j} : Set Vec24) = Set.range ![q j, zM *ᵥ q j] by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]]
  exact this


theorem γ_injective : Function.Injective γ := by decide

@[expose] noncomputable def zE : E := ⟨a 0, a_mem_E 0⟩


end CFSG.Sporadic.Co1Schreier
