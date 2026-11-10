module

public import CFSG.Sporadic.Th.Max3.MaxCheckInputs

public section

namespace CFSG.Sporadic.Th

open Native

section Words

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

@[expose] noncomputable def wordElt (u₁ u₂ : G) (w : List ℕ) : G := (w.map (lettersG u₁ u₂)).prod


end Words

section HElt

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

@[expose] noncomputable def hElt (t : Array (ℕ × ℕ)) (r g₁ g₂ : G) (k : ℕ) : G :=
  if _h : 0 < (t[k]!).1 ∧ (t[k]!).1 - 1 < k then
    lettersG g₁ g₂ (t[k]!).2 * hElt t r g₁ g₂ ((t[k]!).1 - 1) * (lettersG g₁ g₂ (t[k]!).2)⁻¹
  else r
termination_by k


@[expose] noncomputable def hElt2 (t₀ t₁ : Array (ℕ × ℕ)) (r₀ r₁ g₁ g₂ : G) (k : ℕ) : G :=
  if k < t₀.size then hElt t₀ r₀ g₁ g₂ k else hElt t₁ r₁ g₁ g₂ (k - t₀.size)


end HElt


@[expose] noncomputable def hRoot0 : J := wordElt xJ yJ hRootWord0

@[expose] noncomputable def hRoot1 :
    J := wordElt xJ yJ hRootWord1 ^ 9

section Facts


end Facts

end CFSG.Sporadic.Th
