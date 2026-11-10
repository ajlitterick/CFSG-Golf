
module

public import Certificates.Data.Kernel.L5.HFC
public import CFSG.Certificates.Kernel.L5.Fast
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Certificates.Kernel.L5H

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5S
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.GH74.GLS.C3.Layer2.Model

theorem tabL_getD (p : Perm (Fin 16)) (j : Fin 16) : (tabL p).getD j.val 0 = p j := by
  unfold tabL
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
  rfl

theorem tabL_mul (p q : Perm (Fin 16)) : tmulL (tabL p) (tabL q) = tabL (p * q) := by
  unfold tmulL
  conv_lhs => arg 2; unfold tabL
  rw [List.map_map, tabL]
  congr 1
  funext i
  exact tabL_getD p (q i)

theorem tabL_injective : Function.Injective tabL := by
  intro p q h
  ext i
  have := congrArg (fun t => List.getD t i.val 0) h
  simp only [tabL_getD] at this
  rw [this]

theorem tabL_one : tabL 1 = List.finRange 16 := by
  unfold tabL
  simp


theorem mem_fam0 (V : Finset (Fin 16)) : V ∈ fam0 ↔ V ∈ fam0L := by
  simp [fam0, fam0L]

theorem mem_fam1 (V : Finset (Fin 16)) : V ∈ fam1 ↔ V ∈ fam1L := by
  simp [fam1, fam1L]


theorem getD_idxOf {G : List (CV 16)} {x : CV 16} (hx : x ∈ G) :
    G.idxOf x < G.length ∧ G.getD (G.idxOf x) 1 = x := by
  have h := List.idxOf_lt_length_of_mem hx
  exact ⟨h, by rw [List.getD_eq_getElem _ _ h, List.getElem_idxOf]⟩


section Gen


end Gen


end CFSG.Certificates.Kernel.L5H

end
