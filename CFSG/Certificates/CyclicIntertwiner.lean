module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public noncomputable section

namespace CFSG.Certificates

open Matrix

variable {K : Type*} [Field K] {d r : ℕ}


@[expose] def intertwinerSubmodule (A B : Fin r → Matrix (Fin d) (Fin d) K) :
    Submodule K (Matrix (Fin d) (Fin d) K) where
  carrier := {F | ∀ i, F * A i = B i * F}
  add_mem' := by
    intro F G hF hG i
    rw [add_mul, mul_add, hF i, hG i]
  zero_mem' := by
    intro i
    rw [zero_mul, mul_zero]
  smul_mem' := by
    intro c F hF i
    rw [smul_mul_assoc, mul_smul_comm, hF i]


structure IsParentWordFamily (A : Fin r → Matrix (Fin d) (Fin d) K) (p : Fin d → Fin d)
    (ℓ : Fin d → Fin r) (P : Fin d → Matrix (Fin d) (Fin d) K) : Prop where
  parent_lt : ∀ j : Fin d, 0 < j.val → (p j).val < j.val
  root : ∀ j : Fin d, j.val = 0 → P j = 1
  succ : ∀ j : Fin d, 0 < j.val → P j = A (ℓ j) * P (p j)


section family

variable {A B : Fin r → Matrix (Fin d) (Fin d) K} {p : Fin d → Fin d} {ℓ : Fin d → Fin r}
  {P Q : Fin d → Matrix (Fin d) (Fin d) K} {v : Fin d → K}

theorem IsParentWordFamily.intertwine (hP : IsParentWordFamily A p ℓ P)
    (hQ : IsParentWordFamily B p ℓ Q) {F : Matrix (Fin d) (Fin d) K}
    (hF : F ∈ intertwinerSubmodule A B) (j : Fin d) : F * P j = Q j * F := by
  have all : ∀ a : ℕ, ∀ j : Fin d, j.val = a → F * P j = Q j * F := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja
      rcases Nat.eq_zero_or_pos j.val with h0 | hpos
      · rw [hP.root j h0, hQ.root j h0, mul_one, one_mul]
      · rw [hP.succ j hpos, hQ.succ j hpos, ← mul_assoc, hF (ℓ j), mul_assoc,
          ih (p j).val (hja ▸ hP.parent_lt j hpos) (p j) rfl, mul_assoc]
  exact all j.val j rfl


end family


end CFSG.Certificates
