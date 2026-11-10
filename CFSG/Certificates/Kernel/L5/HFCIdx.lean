
module

public import CFSG.Certificates.Kernel.L5.HFCSound
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Certificates.Kernel.L5H

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5S
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.GH74.GLS.C3.Layer2.Model

section Grp

variable {G : List (CV 16)} {n : Nat} {mul : Nat → Nat → Nat} (hl : G.length = n)
  (hnd : G.Nodup) (h1 : (1 : CV 16) ∈ G)
  (hm : ∀ a < n, ∀ b < n, mul a b < n ∧ G.getD a 1 * G.getD b 1 = G.getD (mul a b) 1)

include hl hm in
theorem mulClosed_of_tab : mulClosedChkP G = true := by
  unfold mulClosedChkP
  rw [List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  simp only [decide_eq_true_eq]
  obtain ⟨ia, ea⟩ := getD_idxOf ha
  obtain ⟨ib, eb⟩ := getD_idxOf hb
  obtain ⟨hlt, he⟩ := hm _ (hl ▸ ia) _ (hl ▸ ib)
  rw [← ea, ← eb, he, List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _


end Grp


section G72


end G72


section D8


end D8


end CFSG.Certificates.Kernel.L5H

end
