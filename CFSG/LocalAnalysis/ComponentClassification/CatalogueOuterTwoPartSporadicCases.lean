module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadic
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.PairJ3Pairs
public import CFSG.Sporadic.Schreier.PairHSPairs
public import CFSG.Sporadic.Schreier.PairMcLPairs
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Schreier.Fi24Schreier
public import CFSG.Sporadic.SuzOddCore.Outer
public import CFSG.Monster.B.Fischer.Fi22Model

public section

namespace CFSG.ComponentClassification.CatalogueOuterTwoPart

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


theorem card_outer_fi22 : Nat.card (Outer NativeSporadic.Fi22) = 2 := by
  obtain ⟨⟨e, -⟩, -⟩ := @CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
    NativeSporadic.Fi22 Monster.B.Fischer.fi22P Units.instGroup _ Monster.B.Fischer.fi22PermEquiv
  obtain ⟨f⟩ := Monster.B.Fischer.CTUC_Fi22_full_automorphism_permutation_model.2.2.2.2.2.2.2
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (MulAut Monster.B.Fischer.fi22P ⧸
    (MulAut.conj : Monster.B.Fischer.fi22P →* MulAut Monster.B.Fischer.fi22P).range) = 2
  rw [Nat.card_congr f.toEquiv]
  simp


end CFSG.ComponentClassification.CatalogueOuterTwoPart
