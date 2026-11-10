module

public import Certificates.Kernel.Co2Smith.Mark
public import Certificates.Kernel.Co2Smith.CoxK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem mkT_get {j : Nat} (hj : j < 15) : glMkT[j]! = unpackR 22 (TP j) := by
  have h := tp_k
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hs, h⟩ := h
  obtain ⟨hw, he⟩ := h j hj
  unfold glMkT
  rw [getElem!_pos _ j (by simp [hj]), Array.getElem_ofFn, glR_eq hw]
  exact (eq_unpack_of_eqK he).symm


theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]


end CertificateChecks.KernelCo2Smith
