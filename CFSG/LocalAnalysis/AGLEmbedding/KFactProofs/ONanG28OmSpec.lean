module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28OmCheck

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28

theorem subsetOK_spec {N : ℕ} {sz : ℕ → ℕ} (h : subsetOK N sz = true) :
    ∀ a b c d : Bool, N % (1 + (if a then sz 1 else 0) + (if b then sz 2 else 0) +
      (if c then sz 3 else 0) + (if d then sz 4 else 0)) = 0 →
      (a = false ∧ b = false ∧ c = false ∧ d = false) ∨
        (a = true ∧ b = true ∧ c = true ∧ d = true) := by
  simp only [subsetOK, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  intro a b c d hdiv
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all


theorem epsOK_spec {zc : Array ℕ} {gw : List (List ℕ)} (h : epsOK zc gw = true) :
    ∀ j < 4, mulCode (mulCode (wordCode gw[j]!) zc) (wordCode (gw[j]!).reverse) =
      (if j % 2 = 1 then mulCode zc zc else zc) := by
  simp only [epsOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h


theorem quadOK_spec {zc : Array ℕ} (h : quadOK zc = true) :
    ∀ t < 36, (mulCode zc zc)[t]! ^^^ zc[t]! ^^^ idCode[t]! = 0 := by
  simp only [quadOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h


end CFSG.AGLEmbedding.KFactProofs.G28
