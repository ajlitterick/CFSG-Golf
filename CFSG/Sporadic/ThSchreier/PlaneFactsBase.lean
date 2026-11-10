
module

public import CFSG.Sporadic.ThSchreier.GlobalIndexBase
public meta import CFSG.Sporadic.ThSchreier.Text
public meta import CFSG.Sporadic.ThSchreier.RowBase
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase
public meta import Certificates.Data.CFSGNative.Th.Base
public meta import CFSG.Sporadic.ThSchreier.CentralizerDataBase
public meta import CFSG.Sporadic.ThSchreier.WordsBase

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise


theorem pairwise_lt_of_succ {l : List ℕ}
    (h : ∀ k (hk : k + 1 < l.length), l[k]'(by omega) < l[k + 1]) :
    l.Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  induction j with
  | zero => omega
  | succ j ih =>
    have hs : l[j] < l[j + 1] := h j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact (ih (by omega) h').trans hs
    · subst h'
      exact hs

theorem mem_of_card_eq {n : ℕ} {p : ℕ → Prop} [DecidablePred p] {l : List ℕ}
    (hl : l.Pairwise (· < ·)) (hmem : ∀ x ∈ l, x < n ∧ p x)
    (hcard : ((Finset.range n).filter p).card = l.length) {x : ℕ} (hx : x < n) (hpx : p x) :
    x ∈ l := by
  have hnd : l.Nodup := hl.imp ne_of_lt
  have hsub : l.toFinset ⊆ (Finset.range n).filter p := by
    intro y hy
    rw [List.mem_toFinset] at hy
    rw [Finset.mem_filter, Finset.mem_range]
    exact hmem y hy
  have heq : l.toFinset = (Finset.range n).filter p := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard, List.toFinset_card_of_nodup hnd]
  have hmx : x ∈ (Finset.range n).filter p := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hx, hpx⟩
  rw [← heq, List.mem_toFinset] at hmx
  exact hmx

theorem ncard_fin_mem {n : ℕ} {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < n) :
    {i : Fin n | i.val ∈ l}.ncard = l.length := by
  rw [← List.toFinset_card_of_nodup hnd, ← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun i _ => i.val)
  · intro i hi
    simpa using hi
  · intro i j _ _ h
    exact Fin.ext h
  · intro x hx
    rw [Finset.mem_coe, List.mem_toFinset] at hx
    exact ⟨⟨x, hlt x hx⟩, hx, rfl⟩

theorem getElem!_toArray_eq {l : List ℕ} {k : ℕ} (hk : k < l.length) :
    l.toArray[k]! = l[k] := by
  rw [getElem!_pos l.toArray k (by simpa using hk), List.getElem_toArray]


section Facts

variable (hF : OrbitFacts) (hS : ThScanFacts)
include hF hS

omit hF in
theorem centFixed_sorted : centFixedIdx.Pairwise (· < ·) := by
  refine pairwise_lt_of_succ fun k hk => ?_
  have h := ScanFacts.fixedSorted hS k (by simpa [centFixedArr] using hk)
  rwa [show centFixedArr = centFixedIdx.toArray from rfl,
    getElem!_toArray_eq (by omega : k < centFixedIdx.length), getElem!_toArray_eq hk] at h

omit hF in
theorem centFixed_mem {x : ℕ} (hx : x ∈ centFixedIdx) : x < nX ∧ αIdx x = x := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have h := ScanFacts.fixedMem hS k (by simpa [centFixedArr] using hk)
  rw [show centFixedArr[k]! = centFixedIdx[k] from getElem!_toArray_eq hk] at h
  exact h

omit hF in
theorem fixed_iff_mem {i : ℕ} (hi : i < nX) : αIdx i = i ↔ i ∈ centFixedIdx := by
  constructor
  · intro h
    classical
    refine mem_of_card_eq (n := nX) (p := fun i => αIdx i = i) (centFixed_sorted hS)
      (fun x hx => centFixed_mem hS hx) ?_ hi h
    have h1 := ScanFacts.fixedCount hS
    simpa [centFixedArr] using h1
  · intro h
    exact (centFixed_mem hS h).2

omit hF in
theorem centImage_sorted : centImageIdx.Pairwise (· < ·) := by
  refine pairwise_lt_of_succ fun k hk => ?_
  have h := ScanFacts.imageSorted hS k (by simpa [centImageArr] using hk)
  rwa [show centImageArr = centImageIdx.toArray from rfl,
    getElem!_toArray_eq (by omega : k < centImageIdx.length), getElem!_toArray_eq hk] at h

omit hF in
theorem centImage_mem {k : ℕ} (hk : k < centImageIdx.length) :
    centImageIdx[k] < nX ∧
      rowKeyOf (readKey thSt.keys centImageIdx[k]) = centImageKeys[k]! ∧
      inUA (centImageKeys[k]!).u = true ∧ inUA (centImageKeys[k]!).v = true := by
  have h := ScanFacts.imageMem hS k (by simpa [centImageArr] using hk)
  rw [show centImageArr[k]! = centImageIdx[k] from getElem!_toArray_eq hk] at h
  exact h

end Facts

end CFSG.Sporadic.ThSchreier
