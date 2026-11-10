module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.Quasithin.E6

variable (K : Type) [Field K]

@[expose] def sp4LongRoot : Subgroup ↥(CFSG.Open.StatedSp 2 K) :=
  Subgroup.closure {element | ∃ parameter : K,
    ((element : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.of fun row column => (if row = column then 1 else 0) +
        (if row = Sum.inl 0 ∧ column = Sum.inr 0 then parameter else 0)}

@[expose] def sp4ShortRoot : Subgroup ↥(CFSG.Open.StatedSp 2 K) :=
  Subgroup.closure {element | ∃ parameter : K,
    ((element : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.of fun row column => (if row = column then 1 else 0) +
        (if row = Sum.inl 0 ∧ column = Sum.inl 1 then parameter else 0) -
        (if row = Sum.inr 1 ∧ column = Sum.inr 0 then parameter else 0)}


end CFSG.Quasithin.E6
