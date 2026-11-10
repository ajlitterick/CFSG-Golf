module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
open Matrix

universe u

variable {X : Type u} [Group X]

@[expose] def fischerEUIsPair (E : Set X) : Prop :=
  (∃ e₀ : X, E = {g | IsConj e₀ g}) ∧ (∀ e ∈ E, orderOf e = 2) ∧
    (∀ e ∈ E, ∀ f ∈ E, orderOf (e * f) ∈ ({1, 2, 3} : Set ℕ)) ∧ Subgroup.closure E = ⊤


@[expose] noncomputable def fischerEUHerm (x y : Fin 6 → GaloisField 2 2) : GaloisField 2 2 :=
  ∑ i, x i * y i ^ 2

@[expose] noncomputable def fischerEUSU : Subgroup (GL (Fin 6) (GaloisField 2 2)) :=
  Subgroup.closure {A | (A : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)).det = 1 ∧
    ∀ x y, fischerEUHerm ((A : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)) *ᵥ x)
      ((A : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)) *ᵥ y) = fischerEUHerm x y}

abbrev fischerEUPSU : Type := fischerEUSU ⧸ Subgroup.center fischerEUSU

@[expose] def fischerEUTransvections : Set fischerEUPSU :=
  {y | ∃ A : fischerEUSU, ∃ v : Fin 6 → GaloisField 2 2, v ≠ 0 ∧ fischerEUHerm v v = 0 ∧
    (∀ x, ((A : GL (Fin 6) (GaloisField 2 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)) *ᵥ x =
      x + fischerEUHerm x v • v) ∧ y = QuotientGroup.mk A}


end CFSG.Open
