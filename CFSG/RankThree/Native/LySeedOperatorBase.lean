
module

public import CFSG.RankThree.Native.LySeedCheckInputs
public import CFSG.LinearAlgebra.SelfAdjointIdempotent

@[expose] public section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native Matrix CFSG.LinearAlgebra
open CFSG.Sporadic.He.Native (toMat toMat_mulM toMat_powM toMat_idM toMat_eq_of_beq mulM powM
  idM invM)

theorem toMat_ne_one_of_lyNeId {X : Array (Array ℕ)} (h : lyNeId X = true) :
    toMat 5 111 X ≠ 1 := by
  intro hX
  simp only [lyNeId, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨i, hi, j, hj, hne⟩ := h
  have e := congrFun (congrFun hX ⟨i, hi⟩) ⟨j, hj⟩
  simp only [toMat, of_apply, one_apply, Fin.mk.injEq] at e
  rw [← ZMod.natCast_mod] at e
  apply hne
  split_ifs at e ⊢ with hij
  · have := (ZMod.natCast_eq_natCast_iff' _ 1 5).1 (by rw [e]; rfl)
    rw [Nat.mod_mod] at this
    simpa using this
  · have := (ZMod.natCast_eq_natCast_iff' _ 0 5).1 (by rw [e]; rfl)
    rw [Nat.mod_mod] at this
    simpa using this


section


end


end CFSG.RankThree.Native
