module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProof

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Numbering

variable {Λ : Type*} {n : ℕ}

@[expose] def ggLastEquiv (e : Fin n ≃ Λ) : Fin (n + 1) ≃ Option Λ :=
  finSuccEquivLast.trans (Equiv.optionCongr e)

@[simp] theorem ggLastEquiv_castSucc (e : Fin n ≃ Λ) (i : Fin n) :
    ggLastEquiv e (Fin.castSucc i) = some (e i) := by
  simp [ggLastEquiv, finSuccEquivLast_castSucc]

@[simp] theorem ggLastEquiv_last (e : Fin n ≃ Λ) : ggLastEquiv e (Fin.last n) = none := by
  simp [ggLastEquiv, finSuccEquivLast_last]

@[expose] def ggFirstEquiv (e : Fin n ≃ Λ) : Fin (n + 1) ≃ Option Λ :=
  (finSuccEquiv n).trans (Equiv.optionCongr e)

@[simp] theorem ggFirstEquiv_zero (e : Fin n ≃ Λ) : ggFirstEquiv e 0 = none := by
  simp [ggFirstEquiv, finSuccEquiv_zero]

@[simp] theorem ggFirstEquiv_succ (e : Fin n ≃ Λ) (i : Fin n) :
    ggFirstEquiv e i.succ = some (e i) := by
  simp [ggFirstEquiv, finSuccEquiv_succ]

theorem ggMatrix_eq_reindex {ι κ : Type*} {P : Matrix κ κ ℤ} {Q : Matrix ι ι ℤ} (f : ι ≃ κ)
    (h : ∀ i j, P (f i) (f j) = Q i j) : P = Matrix.reindex f f Q := by
  ext γ γ'
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, ← h, f.apply_symm_apply, f.apply_symm_apply]

end Numbering

@[expose] def GGForkShapeA {Λ : Type*} (C : Matrix Λ Λ ℤ) (b : Λ) : Prop :=
  ∃ (m : ℕ) (e : Fin (m + 1) ≃ Λ), 2 ≤ m ∧ e (Fin.last m) = b ∧
    ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j

section ShapeA

variable {Λ : Type*} {C : Matrix Λ Λ ℤ} {m : ℕ} {e : Fin (m + 1) ≃ Λ}

theorem eq_of_forkShapeA (hm : 1 ≤ m) {b c : Λ} (hb : e (Fin.last m) = b)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j) (hbc : C b c = -1) :
    c = e ⟨m - 1, by omega⟩ := by
  have h := hC (Fin.last m) (e.symm c)
  rw [hb, e.apply_symm_apply, hbc] at h
  have hk := (e.symm c).isLt
  have hval : ((e.symm c) : ℕ) = m - 1 := by
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_last] at h
    split_ifs at h
    omega
  rw [← e.apply_symm_apply c]
  exact congrArg e (Fin.ext hval)

variable [DecidableEq Λ]

theorem ggAttachCartan_forkShapeA_c (hm : 2 ≤ m)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j) :
    ggAttachCartan C (e ⟨m - 1, by omega⟩) =
      Matrix.reindex (ggLastEquiv e) (ggLastEquiv e) (CartanMatrix.D (m + 2)) := by
  refine ggMatrix_eq_reindex _ fun i j => ?_
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [CartanMatrix.D]
    | cast j =>
      have hj := j.isLt
      simp only [ggLastEquiv_last, ggLastEquiv_castSucc, ggAttachCartan_none_some,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,
        Fin.val_last, Fin.val_castSucc, or_true, and_true]
      split_ifs <;> omega
  | cast i =>
    have hi := i.isLt
    induction j using Fin.lastCases with
    | last =>
      simp only [ggLastEquiv_last, ggLastEquiv_castSucc, ggAttachCartan_some_none,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,
        Fin.val_last, Fin.val_castSucc, or_true, and_true]
      split_ifs <;> omega
    | cast j =>
      have hj := j.isLt
      simp only [ggLastEquiv_castSucc, ggAttachCartan_some_some, hC, CartanMatrix.A,
        CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc]
      split_ifs <;> omega

theorem ggAttachCartan_forkShapeA_b (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j) :
    ggAttachCartan C (e (Fin.last m)) =
      Matrix.reindex (ggLastEquiv e) (ggLastEquiv e) (CartanMatrix.A (m + 2)) := by
  refine ggMatrix_eq_reindex _ fun i j => ?_
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [CartanMatrix.A]
    | cast j =>
      have hj := j.isLt
      simp only [ggLastEquiv_last, ggLastEquiv_castSucc, ggAttachCartan_none_some,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff,
        Fin.val_last, Fin.val_castSucc]
      split_ifs <;> omega
  | cast i =>
    have hi := i.isLt
    induction j using Fin.lastCases with
    | last =>
      simp only [ggLastEquiv_last, ggLastEquiv_castSucc, ggAttachCartan_some_none,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff,
        Fin.val_last, Fin.val_castSucc]
      split_ifs <;> omega
    | cast j =>
      have hj := j.isLt
      simp only [ggLastEquiv_castSucc, ggAttachCartan_some_some, hC, CartanMatrix.A,
        Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc]

end ShapeA

section Weyl

variable {Λ : Type} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {m : ℕ} {e : Fin (m + 1) ≃ Λ}

theorem exists_weyl_ggAttachCartan_forkShapeA_c (hm : 2 ≤ m)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j) :
    ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
      GGIntCartan M' (ggAttachCartan C (e ⟨m - 1, by omega⟩)) :=
  ⟨(ggCoxeterMatrixD (m + 2)).reindex (ggLastEquiv e),
    Or.inl ⟨m + 2, ggLastEquiv e, by omega, Or.inr (Or.inr ⟨by omega, rfl⟩)⟩,
    by rw [ggAttachCartan_forkShapeA_c hm hC]; exact (ggIntCartan_D (m + 2)).reindex _⟩

theorem exists_weyl_ggAttachCartan_forkShapeA_b
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j) :
    ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
      GGIntCartan M' (ggAttachCartan C (e (Fin.last m))) :=
  ⟨(CoxeterMatrix.A (m + 2)).reindex (ggLastEquiv e),
    Or.inl ⟨m + 2, ggLastEquiv e, by omega, Or.inl rfl⟩,
    by rw [ggAttachCartan_forkShapeA_b hC]; exact (ggIntCartan_A (m + 2)).reindex _⟩

end Weyl

section Chain


end Chain


end CFSG.StandardType
