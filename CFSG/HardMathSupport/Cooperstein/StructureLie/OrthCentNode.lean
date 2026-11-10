module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthCentLift
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthCentRoots

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin

theorem kap_surj {n : ℕ} (r : Fin n ⊕ Fin n) : ∃ b t, r = kap b t := by
  rcases r with b | b
  · exact ⟨b, true, rfl⟩
  · exact ⟨b, false, rfl⟩

theorem exists_two_ne {n : ℕ} (hn : 3 ≤ n) (a : Fin n) :
    ∃ b₁ b₂ : Fin n, b₁ ≠ a ∧ b₂ ≠ a ∧ b₁ ≠ b₂ := by
  by_cases h0 : a.val = 0
  · exact ⟨⟨1, by omega⟩, ⟨2, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega,
      fun e => by simp [Fin.ext_iff] at e; omega, fun e => by simp [Fin.ext_iff] at e⟩
  · by_cases h1 : a.val = 1
    · exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega,
        fun e => by simp [Fin.ext_iff] at e; omega, fun e => by simp [Fin.ext_iff] at e⟩
    · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega,
        fun e => by simp [Fin.ext_iff] at e; omega, fun e => by simp [Fin.ext_iff] at e⟩

section Node


end Node

end CFSG.HardMathSupport.Cooperstein.StructureLie
