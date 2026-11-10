module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreMain
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NB
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NCore

public section

namespace CFSG.ClassicalInvolution.Hat2A7R

open CFSG.ClassicalInvolution

theorem a7ThmI_of_inductive2A7 (h : Hat2A7.CITInductive2A7) : A7ThmI := by
  intro F _ _ _ hnab K z hw hyp
  obtain ⟨L, hL⟩ := Hat2A7.exists_isClassical2A7_of_witness hyp.orderOf_eq_two hyp.mem
    hyp.subnormal hw
  exact (Hat2A7.false_of_inductive2A7 h hnab hL).elim

theorem a7ThmI_of_coreStep2A7 (h : Hat2A7.CoreStep2A7) : A7ThmI :=
  a7ThmI_of_inductive2A7 (Hat2A7.citInductive2A7_of_coreStep h)


end CFSG.ClassicalInvolution.Hat2A7R
