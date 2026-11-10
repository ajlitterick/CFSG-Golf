module

public import CFSG.LocalAnalysis.StandardType.GGReeB2CondCDefs

public section

namespace CFSG.StandardType.ReeB2Fixed

@[expose] def resolve (e : ℕ) (A B : Finset (Fin e)) : Finset (Fin e) :=
  symmDiff A B ∪ ((A ∩ B).filter fun p => succσ e p ∉ B).image (succσ e)

@[expose] def SyncAt (e : ℕ) (A B : Finset (Fin e)) (p : Fin e) : Prop :=
  p ∉ A ∧ p ∉ B ∧ (succσ e p ∈ A ↔ succσ e p ∈ B)


end CFSG.StandardType.ReeB2Fixed
