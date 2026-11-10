module

public import CFSG.ClassicalInvolution.Uniform.UThmStmtB

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly
open scoped MatrixGroups

section IH8

variable (p f : ℕ) [Fact p.Prime]

structure IH8T (n : ℕ) : Prop where
  thm2 : Thm2BelowU p f n
  thm4 : Thm4BelowU p f n
  thm5 : Thm5BelowU p f n
  thm6 : Thm6TypedBelowU p f n
  thm7 : Thm7TypedBelowU p f n
  thm8 : Thm8TypedBelowU p f n
  muTable : MuTableBelowU p f n
  thm3 : Thm3TypedBelowExactU p f n


variable {p f}


end IH8

section Rest

variable (p f : ℕ) [Fact p.Prime]

@[expose] def IHInterfaceU : Prop :=
  ∀ n : ℕ, CITBelowT (.sl2 p f) n → Thm4BelowU p f n ∧ Thm2BelowU p f n

@[expose] def IH8RestU : Prop :=
  ∀ n : ℕ, CITBelowT (.sl2 p f) n →
    Thm5BelowU p f n ∧ Thm6TypedBelowU p f n ∧ Thm7TypedBelowU p f n ∧ Thm8TypedBelowU p f n ∧
      MuTableBelowU p f n ∧ Thm3TypedBelowExactU p f n

variable {p f}

theorem ih8T_of_rest (hI : IHInterfaceU p f) (h : IH8RestU p f) {n : ℕ}
    (hn : CITBelowT (.sl2 p f) n) : IH8T p f n :=
  have h24 := hI n hn
  have h5 := h n hn
  ⟨h24.2, h24.1, h5.1, h5.2.1, h5.2.2.1, h5.2.2.2.1, h5.2.2.2.2.1, h5.2.2.2.2.2⟩


end Rest

section Stand


end Stand

end CFSG.ClassicalInvolution.Uniform
