
module

public import CFSG.RankThree.Native.LySeedOperatorBase

public import CFSG.RankThree.Native.LySeedCheck

public section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native Matrix CFSG.LinearAlgebra
open CFSG.Sporadic.He.Native (toMat toMat_mulM toMat_powM toMat_idM toMat_eq_of_beq mulM powM
  idM invM)

theorem ly_seed_parts :
    lyCheckAB14 = true ∧ lyCheckAB7 = true ∧ lyCheckAB2 = true ∧ lyCheckA = true ∧
      lyCheckB = true ∧ lyCheckX = true ∧ lyCheckFsymm = true ∧ lyCheckFinv = true ∧
      lyCheckS = true ∧ lyCheckE = true := by
  have h := ly_seed_check
  simp only [lySeedChecks, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩


theorem lyF_symm : lyFᵀ = lyF := by
  have e := toMat_eq_of_beq (p := 5) (d := 111)
    (show (transM formF == formF) = true from ly_seed_parts.2.2.2.2.2.2.1)
  rw [toMat_transM] at e
  exact e


end CFSG.RankThree.Native
