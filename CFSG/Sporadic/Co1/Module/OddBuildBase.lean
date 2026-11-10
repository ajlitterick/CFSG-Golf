
module

public import CFSG.Sporadic.Co1.Module.OddChecksInputs
public import Certificates.Data.Kernel.Co1M.Odd73
public import Certificates.Data.Kernel.Co1Odd71Data

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix CFSG.KC.Odd73 CFSG.KC.Co1F2 CFSG.KD.Co1Odd

attribute [local instance] vecAct vecSMul

attribute [local irreducible] rr regsRows


theorem reg_comm
    {i j : ℕ} (h : mulRows 24 (rr i) (rr j) = mulRows 24 (rr j) (rr i)) :
    reg i * reg j = reg j * reg i := by
  apply mat_injective
  rw [map_mul, map_mul, mat_reg, mat_reg, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, h]

theorem reg_mul_eq_one
    {i j : ℕ} (h : mulRows 24 (rr i) (rr j) = idRows 24) :
    reg i * reg j = 1 := by
  apply mat_injective
  rw [map_mul, mat_reg, mat_reg, ← rowsMatrix_mulRows, h, rowsMatrix_idRows, map_one]

theorem reg_inv
    {i j : ℕ} (h : mulRows 24 (rr i) (rr j) = idRows 24) : (reg i)⁻¹ = reg j :=
  inv_eq_of_mul_eq_one_right (reg_mul_eq_one h)


@[expose] noncomputable def omega0 : Vec24 := toVecD 24 code4

theorem reg_fix
    {i : ℕ} (h : isFixedN (Mt i) code4 = true) : reg i • omega0 = omega0 := by
  rw [smul_eq_co1Act, omega0, co1Act_eq_mulVec, mat_reg]
  exact (isFixedN_iff (rr i) (by norm_num [code4])).1 h

@[expose] noncomputable def n1 : NativeSporadic.Co1 := reg 23

@[expose] noncomputable def n2 : NativeSporadic.Co1 := reg 17

@[expose] noncomputable def rho3 : NativeSporadic.Co1 := reg 27

@[expose] noncomputable def t1 : NativeSporadic.Co1 := reg 86

@[expose] noncomputable def sRep
    (k : Fin 3) : NativeSporadic.Co1 := reg (sIdx[(k : ℕ)]!)

noncomputable abbrev Hst : Subgroup NativeSporadic.Co1 :=
  MulAction.stabilizer NativeSporadic.Co1 omega0


theorem pairFixOK_facts {k fx f4 : ℕ} (h : pairFixOK k fx f4 = true) :
    fixCount [Mt 27, Mt (sIdx[k]!)] = fx ∧
    fixCount4 [Mt 27, Mt (sIdx[k]!)] (transposeRows 24 qRows) (orbitOf 2 98280).pts
      (posTable 24 (orbitOf 2 98280).pts) 98280 = f4 := by
  simp only [pairFixOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h


theorem smul_reg_iff (i : ℕ) (v : Vec24) :
    reg i • v = v ↔ rowsMatrix 24 (rr i) *ᵥ v = v := by
  rw [smul_eq_co1Act, co1Act_eq_mulVec, mat_reg]

theorem reg_mem_centralizer {i : ℕ}
    (h : mulRows 24 (rr i) (rr 27) = mulRows 24 (rr 27) (rr i)) :
    reg i ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact reg_comm h


theorem finite_co1 : Finite NativeSporadic.Co1 :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)


theorem forall_mem_two {α : Type*} (p : α → Prop) (a b : α) :
    (∀ x ∈ [a, b], p x) ↔ p a ∧ p b := by simp

theorem gram_nondeg {k : ℕ}
    (hk : gramOK (transposeRows 24 f0Rows) (Wk k) = true) :
    ∀ u ∈ {v : Vec24 | reg 27 • v = v ∧ reg (sIdx[k]!) • v = v},
      (∀ v ∈ {v : Vec24 | reg 27 • v = v ∧ reg (sIdx[k]!) • v = v}, bil₀ u v = 0) → u = 0 := by
  have h := nondeg_of_gramOK (Ms := [rr 27, rr (sIdx[k]!)]) hk
  have e : {v : Vec24 | ∀ M ∈ [rr 27, rr (sIdx[k]!)], rowsMatrix 24 M *ᵥ v = v} =
      {v : Vec24 | reg 27 • v = v ∧ reg (sIdx[k]!) • v = v} := by
    ext v
    simp only [Set.mem_ofPred_eq, forall_mem_two]
    rw [smul_reg_iff, smul_reg_iff]
  rw [e] at h
  exact h

theorem sIdx_J73 {k : ℕ} (hk : k < 3) : sIdx[k]! = getL 0 J73 k := by
  interval_cases k <;> rfl

end CFSG.Sporadic.Co1.Module.Odd
