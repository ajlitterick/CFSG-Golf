module

public import CFSG.ClassicalInvolution.Models.LinearFrames.BlockConj
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.Models.LinearPairs.Intrinsic

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ClassicalInvolution.Phan (blockMat)
open scoped MatrixGroups

section Basic

variable (K : Type) [Field K] (n : ℕ)

@[expose] def slMat : SL(n, K) →* Matrix (Fin n) (Fin n) K where
  toFun g := (g : Matrix (Fin n) (Fin n) K)
  map_one' := Matrix.SpecialLinearGroup.coe_one
  map_mul' := Matrix.SpecialLinearGroup.coe_mul

variable {K n}

@[simp] theorem slMat_apply (g : SL(n, K)) : slMat K n g = (g : Matrix (Fin n) (Fin n) K) := rfl

theorem slMat_injective : Function.Injective (slMat K n) := Subtype.coe_injective

variable (K n) in
@[expose] def signGroup : Subgroup SL(n, K) := signSubgroup (slMat K n)

theorem mem_signGroup {x : SL(n, K)} :
    x ∈ signGroup K n ↔ IsSignDiag (x : Matrix (Fin n) (Fin n) K) :=
  Iff.rfl


theorem signGroup_comm {x y : SL(n, K)} (hx : x ∈ signGroup K n) (hy : y ∈ signGroup K n) :
    x * y = y * x :=
  signSubgroup_comm slMat_injective hx hy

variable (K) in
@[expose] def zElt (T : Pair n) : SL(n, K) :=
  ⟨zMat K n T.1, by rw [det_zMat, T.2]; norm_num⟩

theorem coe_zElt (T : Pair n) : ((zElt K T : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
    zMat K n T.1 := rfl

theorem zElt_mem_signGroup (T : Pair n) : zElt K T ∈ signGroup K n :=
  isSignDiag_zMat T.1

theorem zElt_mul_self (T : Pair n) : zElt K T * zElt K T = 1 :=
  Subtype.ext (zMat_mul_self T.1)

theorem zElt_injective (h2 : (2 : K) ≠ 0) : Function.Injective (zElt K (n := n)) := by
  intro T T' h
  exact Subtype.ext (zMat_inj h2 (congrArg Subtype.val h))

variable (K) in
@[expose] def Lc (T : Pair n) : Subgroup SL(n, K) := longRootGroup (zMat K n T.1)

theorem mem_Lc {T : Pair n} {x : SL(n, K)} : x ∈ Lc K T ↔
    (x : Matrix (Fin n) (Fin n) K) * zMat K n T.1 = zMat K n T.1 * x ∧
      (x : Matrix (Fin n) (Fin n) K) * (1 + zMat K n T.1) = 1 + zMat K n T.1 :=
  Iff.rfl

theorem negBlock_eq_zMat {j : ℕ} (hj : j + 2 ≤ n) :
    negBlock K n j = zMat K n {⟨j, by omega⟩, ⟨j + 1, by omega⟩} := by
  rw [negBlock_eq_diagonal, zMat]
  congr 1
  funext a
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  by_cases h : j ≤ a.val ∧ a.val < j + 2
  · rw [ite_eq_left h, ite_eq_left]
    omega
  · rw [ite_eq_right h, ite_eq_right]
    omega

end Basic


section Monomial

variable {K : Type} [Field K] {n : ℕ}

theorem exists_monomial_pair (hn : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ∃ (g : SL(n, K)) (τ : Equiv.Perm (Fin n)), IsMonomialFor (g : Matrix (Fin n) (Fin n) K) τ ∧
      τ ⟨0, by omega⟩ = i ∧ τ ⟨1, by omega⟩ = j := by
  obtain ⟨τ, h0, h1⟩ := exists_perm_pair hn hij
  exact ⟨⟨monoMat K τ, det_monoMat (by omega) τ⟩, τ, isMonomialFor_monoMat τ, h0, h1⟩

theorem exists_monomial_of_pair (hn : 2 ≤ n) (T : Pair n) :
    ∃ (g : SL(n, K)) (τ : Equiv.Perm (Fin n)), IsMonomialFor (g : Matrix (Fin n) (Fin n) K) τ ∧
      T.1 = {τ ⟨0, by omega⟩, τ ⟨0 + 1, by omega⟩} := by
  obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp T.2
  obtain ⟨g, τ, hg, h0, h1⟩ := exists_monomial_pair (K := K) hn hij
  refine ⟨g, τ, hg, ?_⟩
  rw [hT, ← h0]
  congr 2
  exact h1.symm

theorem monomial_conj_negBlock {g : SL(n, K)} {τ : Equiv.Perm (Fin n)}
    (hg : IsMonomialFor (g : Matrix (Fin n) (Fin n) K) τ) {j : ℕ} (hj : j + 2 ≤ n) :
    (g : Matrix (Fin n) (Fin n) K) * negBlock K n j * ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K)
      = zMat K n {τ ⟨j, by omega⟩, τ ⟨j + 1, by omega⟩} := by
  rw [negBlock_eq_zMat hj, hg.mul_zMat_mul_inv (coe_mul_coe_inv g)]
  simp [Finset.map_insert]

theorem Lc_eq_map_conj (h2 : (2 : K) ≠ 0) {g : SL(n, K)} {τ : Equiv.Perm (Fin n)}
    (hg : IsMonomialFor (g : Matrix (Fin n) (Fin n) K) τ) {j : ℕ} (hj : j + 2 ≤ n) {T : Pair n}
    (hT : T.1 = {τ ⟨j, by omega⟩, τ ⟨j + 1, by omega⟩}) :
    Lc K T = (blockSL K n 2 j hj).range.map (MulAut.conj g).toMonoidHom := by
  rw [range_blockSL_eq_longRootGroup h2 hj, ← longRootGroup_conj, monomial_conj_negBlock hg hj,
    ← hT]
  rfl

theorem isLongRootSL2_Lc (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) (T : Pair n) :
    IsLongRootSL2 hn (Lc K T) (zElt K T) := by
  obtain ⟨g, τ, hg, hT⟩ := exists_monomial_of_pair (K := K) hn T
  refine ⟨g, Lc_eq_map_conj h2 hg (by omega : 0 + 2 ≤ n) hT, ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rootInv,
    monomial_conj_negBlock hg (by omega : 0 + 2 ≤ n), coe_zElt, hT]

end Monomial

section Entries

variable {K : Type} [Field K] {n : ℕ}

abbrev ent (e : SL(n, K)) (a : Fin n) : K := entOf (slMat K n) e a

theorem ent_cases {e : SL(n, K)} (he : e ∈ signGroup K n) (a : Fin n) :
    ent e a = 1 ∨ ent e a = -1 :=
  entOf_cases he a

theorem ent_mul_self {e : SL(n, K)} (he : e ∈ signGroup K n) (a : Fin n) :
    ent e a * ent e a = 1 :=
  entOf_mul_self he a

theorem coe_eq_diagonal {e : SL(n, K)} (he : e ∈ signGroup K n) :
    (e : Matrix (Fin n) (Fin n) K) = Matrix.diagonal (ent e) :=
  mat_eq_diagonal he

theorem ent_mul {e f : SL(n, K)} (he : e ∈ signGroup K n) (hf : f ∈ signGroup K n) (a : Fin n) :
    ent (e * f) a = ent e a * ent f a :=
  entOf_mul he hf a


theorem inv_eq_self_of_mem {e : SL(n, K)} (he : e ∈ signGroup K n) : e⁻¹ = e :=
  inv_eq_self_of_mem_signSubgroup slMat_injective he


end Entries

section Chart

variable {K : Type} [Field K] {n : ℕ}

@[expose] def chart (hn : 2 ≤ n) (g : SL(n, K)) : SL(2, K) →* SL(n, K) :=
  (MulAut.conj g).toMonoidHom.comp (blockSL K n 2 0 (by omega))


theorem diagonal_two_mul_self {a b : K} (ha : a * a = 1) (hb : b * b = 1) :
    Matrix.diagonal ![a, b] * Matrix.diagonal ![a, b] = (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [ha, hb]

@[expose] def signGL2 {a b : K} (ha : a * a = 1) (hb : b * b = 1) : GL (Fin 2) K :=
  ⟨Matrix.diagonal ![a, b], Matrix.diagonal ![a, b], diagonal_two_mul_self ha hb,
    diagonal_two_mul_self ha hb⟩

theorem coe_signGL2 {a b : K} (ha : a * a = 1) (hb : b * b = 1) :
    ((signGL2 ha hb : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![a, b] := rfl

theorem coe_signGL2_inv {a b : K} (ha : a * a = 1) (hb : b * b = 1) :
    (((signGL2 ha hb)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![a, b] :=
  rfl

end Chart

section Diag

variable {K : Type} [Field K] {n : ℕ}

theorem zElt_ent (T : Pair n) (a : Fin n) :
    ent (zElt K T) a = if a ∈ T.1 then -1 else 1 :=
  zMat_apply_self T.1 a

theorem coe_conj_blockSL (hn : 2 ≤ n) {e : SL(n, K)} (he : e ∈ signGroup K n) (s : SL(2, K)) :
    ((e * blockSL K n 2 0 (by omega) s * e⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      blockMat n 0 (Matrix.diagonal ![ent e ⟨0, by omega⟩, ent e ⟨1, by omega⟩] *
        (s : Matrix (Fin 2) (Fin 2) K) *
          Matrix.diagonal ![ent e ⟨0, by omega⟩, ent e ⟨1, by omega⟩]) := by
  rw [inv_eq_self_of_mem he, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_blockSL, coe_eq_diagonal he]
  exact diagonal_conj_blockMat_two hn (ent_mul_self he) _

theorem conj_blockSL_eq (hn : 2 ≤ n) {e : SL(n, K)} (he : e ∈ signGroup K n) (s : SL(2, K)) :
    e * blockSL K n 2 0 (by omega) s * e⁻¹ =
      blockSL K n 2 0 (by omega) (slConjugation 2 K
        (signGL2 (ent_mul_self he ⟨0, by omega⟩) (ent_mul_self he ⟨1, by omega⟩)) s) := by
  apply Subtype.ext
  rw [coe_conj_blockSL hn he s, coe_blockSL, slConjugation_matrix, coe_signGL2,
    coe_signGL2_inv]

end Diag

section DiagDataSection

variable {K : Type} [Field K] {n : ℕ}

@[expose] def transvec2 : SL(2, K) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_transvec2 : ((transvec2 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := rfl


theorem neg_eq_iff_not_eq_of_sign (h2 : (2 : K) ≠ 0) {x y : K} (hx : x = 1 ∨ x = -1)
    (hy : y = 1 ∨ y = -1) : -x = y ↔ ¬ x = y := by
  have h2' : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [h2', h2'.symm]


end DiagDataSection

section Sigma


end Sigma

end CFSG.ClassicalInvolution.Models
