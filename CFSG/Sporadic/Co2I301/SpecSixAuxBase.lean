
module

public import CFSG.Sporadic.Co2Schreier.SixGroup
public import CFSG.Sporadic.Co2I301.Inputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2I301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
  CFSG.Sporadic.SmallF2 CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.HardMathSupport.Dickson.I271
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (basisMatrixEquiv
  basisMatrixEquiv_mulVec basisMatrixEquiv_val)
open scoped Matrix

private theorem getD_find?_range_lt {n : ℕ} (hn : 0 < n) (f : ℕ → Bool) :
    ((List.range n).find? f).getD 0 < n := by
  cases h : (List.range n).find? f with
  | none => simpa using hn
  | some m => simpa using List.mem_of_find?_eq_some h

private theorem sixCoord_lt (x : ℕ) : sixCoord x < 64 :=
  getD_find?_range_lt (by norm_num) _

private theorem sixCols_size (t : Array ℕ) : (sixCols t).size = 6 := by
  simp [sixCols]

private theorem sixCols_get (t : Array ℕ) {k : ℕ} (hk : k < 6) :
    (sixCols t)[k]! = sixCoord (sixImage t k) := by
  rw [sixCols, getElem!_pos _ k (by simpa using hk)]
  simp

private theorem sixCols_lt (t : Array ℕ) : ∀ k < (sixCols t).size, (sixCols t)[k]! < 2 ^ 6 := by
  intro k hk
  rw [sixCols_size] at hk
  rw [sixCols_get t hk]
  exact sixCoord_lt _

private theorem sixColsOK_spec {t : Array ℕ} (h : sixColsOK t = true) {k : ℕ} (hk : k < 6) :
    xorBits sixPacked (sixCols t)[k]! = sixImage t k :=
  beq_iff_eq.1 (allLt_spec h hk)

private theorem toVecD_xorBits_cols {cs : Array ℕ} (hc : cs.size = 6) (x : ℕ) :
    toVecD 6 (xorBits cs x) =
      (Matrix.of fun j k : Fin 6 => toVecD 6 cs[(k : ℕ)]! j) *ᵥ toVecD 6 x := by
  rw [xorBits, foldl_xor_toVecD, toVecD_zero, zero_add]
  funext j
  rw [Matrix.mulVec, dotProduct, Finset.sum_apply, hc, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.of_apply, toVecD_apply 6 x k]
  by_cases hx : x.testBit k
  · simp [hx]
  · simp [hx]

private theorem perm63Of_get (t : Array ℕ) {p : ℕ} (hp : p < 63) :
    (perm63Of t)[p]! = xorBits (sixCols t) (p + 1) - 1 := by
  change (Array.ofFn (n := 63) fun q : Fin 63 => xorBits (sixCols t) (q.val + 1) - 1)[p]! = _
  rw [getElem!_ofFn_nat _ hp]

private theorem perm63Of_lt (t : Array ℕ) {p : ℕ} (hp : p < 63) : (perm63Of t)[p]! < 63 := by
  rw [perm63Of_get t hp]
  have := xorBits_lt (sixCols_lt t) (p + 1)
  norm_num at this
  omega

section Action

theorem sixAction_sixBasis_cols (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) (hok : sixColsOK t = true) (k : Fin 6) :
    sixAction c (sixBasis k) = ∑ j : Fin 6, toVecD 6 (sixCols t)[(k : ℕ)]! j • sixBasis j := by
  apply Subtype.ext
  rw [sixAction_apply, sixBasis_apply, linC_sixVec, ← toVecD_sixImage ht k,
    ← sixColsOK_spec hok k.2, ← sum_sixVec, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, sixBasis_apply, toVecD_apply]
  split_ifs <;> simp

theorem toMatrix_sixAction_cols (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) (hok : sixColsOK t = true) :
    LinearMap.toMatrix sixBasis sixBasis (sixAction c : V6 →ₗ[ZMod 2] V6) =
      Matrix.of fun j k : Fin 6 => toVecD 6 (sixCols t)[(k : ℕ)]! j := by
  ext j k
  rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, sixAction_sixBasis_cols c ht hok,
    Module.Basis.repr_sum_self, Matrix.of_apply]

private theorem equivFun_sixAction_sixPt (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) (hok : sixColsOK t = true) (p : ℕ) :
    sixBasis.equivFun (sixAction c (sixPt p)) = toVecD 6 (xorBits (sixCols t) (p + 1)) := by
  rw [← basisMatrixEquiv_mulVec sixBasis (sixAction c) (sixPt p), basisMatrixEquiv_val,
    toMatrix_sixAction_cols c ht hok, sixPt, LinearEquiv.apply_symm_apply,
    ← toVecD_xorBits_cols (sixCols_size t)]

private theorem xorBits_sixCols_ne_zero (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) (hok : sixColsOK t = true) {p : ℕ}
    (hp : p < 63) : xorBits (sixCols t) (p + 1) ≠ 0 := by
  intro h0
  have h := equivFun_sixAction_sixPt c ht hok p
  rw [h0, toVecD_zero] at h
  have h1 : sixAction c (sixPt p) = 0 :=
    sixBasis.equivFun.injective (by rw [h, map_zero])
  exact sixPt_ne_zero hp ((LinearEquiv.map_eq_zero_iff _).1 h1)

theorem sixAction_sixPt_cols (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) (hok : sixColsOK t = true) {p : ℕ}
    (hp : p < 63) : sixAction c (sixPt p) = sixPt ((perm63Of t)[p]!) := by
  apply sixBasis.equivFun.injective
  rw [equivFun_sixAction_sixPt c ht hok p, sixPt, LinearEquiv.apply_symm_apply,
    perm63Of_get t hp]
  have := xorBits_sixCols_ne_zero c ht hok hp
  congr 1
  omega

theorem rep_perm63Of (c : locC) {t : Array ℕ} (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300)))
    (hok : sixColsOK t = true) : Rep 63 (perm63Of t) (toPerm63 (sixAction c)) := by
  intro x
  have h1 := congrArg Subtype.val (toPerm63_apply (sixAction c) x)
  change sixPt (toPerm63 (sixAction c) x : ℕ) = sixAction c (sixPt x) at h1
  rw [sixAction_sixPt_cols c ht hok x.2] at h1
  exact sixPt_injective (perm63Of_lt t x.2) (toPerm63 (sixAction c) x).2 h1.symm

end Action

private theorem rep_word63_foldl {g : Array (Array ℕ)} {Y : List (Equiv.Perm (Fin 63))} :
    ∀ (w : List ℕ) (acc : Array ℕ) (A : Equiv.Perm (Fin 63)), Rep 63 acc A →
      (∀ i ∈ w, Rep 63 g[i]! (Y.getD i 1)) →
      Rep 63 (w.foldl (fun acc i => compA 63 acc g[i]!) acc)
        (A * (w.map fun i => Y.getD i 1).prod)
  | [], acc, A, hA, _ => by simpa using hA
  | i :: w, acc, A, hA, hw => by
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact rep_word63_foldl w _ _ (rep_compA hA (hw i List.mem_cons_self))
      fun j hj => hw j (List.mem_cons_of_mem _ hj)

theorem rep_word63 {g : Array (Array ℕ)} {Y : List (Equiv.Perm (Fin 63))} (w : List ℕ)
    (hw : ∀ i ∈ w, Rep 63 g[i]! (Y.getD i 1)) :
    Rep 63 (word63 g w) ((w.map fun i => Y.getD i 1).prod) := by
  have := rep_word63_foldl w (idA 63) 1 rep_idA hw
  rw [one_mul] at this
  exact this


section Small

end Small

private theorem hl63_size : (hl63 ()).size = hlWords.length := by
  simp [hl63]

private theorem hl63_get {t : ℕ} (ht : t < hlWords.length) :
    (hl63 ())[t]! = word63 #[perm63Of (i301K1 ()), perm63Of (i301K2 ()), perm63Of (i301D ())]
      (hlWords.getD t []) := by
  rw [List.getD_eq_getElem _ _ ht, getElem!_pos _ t (by rw [hl63_size]; exact ht)]
  simp [hl63]

private theorem hlWords_letters : ∀ w ∈ hlWords, ∀ i ∈ w, i < 3 := by
  decide

section Main

end Main

end CFSG.Sporadic.Co2I301
