module

public import CFSG.LocalAnalysis.SectionRank.QTK.List
public import CFSG.LocalAnalysis.SectionRank.QTK.Basic

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Assembly.LowTwoRank


@[expose] def QTExceptionalList (S : Type) [Group S] : Prop :=
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ChevalleyExceptionalModel S .G2 p 1) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
    (∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
    (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f) ∨
    ReeTitsModel S .Tits 2 1 ∨
    (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ SuzukiModel S 2 f)


end CFSG.SectionRank.QTK
