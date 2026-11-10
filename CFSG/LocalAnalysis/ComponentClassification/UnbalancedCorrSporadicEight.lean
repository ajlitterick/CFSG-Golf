module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSporadicDihedral
public import CFSG.Sporadic.GLQ.J4TwoRank
public import CFSG.Sporadic.GLQ.HNTwoRank
public import CFSG.Sporadic.GLQ.BTwoRank
public import CFSG.Sporadic.GLQ.MonsterTwoRank
public import CFSG.Sporadic.Schreier.LySylow
public import CFSG.Sporadic.Schreier.ONLocalOrders
public import CFSG.Sporadic.Bridge.MonsterModels

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Blueprint Blueprint.NativeSporadic

@[expose] def ONSylowCharacteristicElementaryEight : Prop :=
  Nat.card (Subgroup.closure {x | ∃ t ∈ ONSchreier.onT, t ^ 2 = x}) = 64 ∧
    IsElementaryAbelian 2 (Subgroup.closure
      {x | x ∈ Subgroup.closure {x | ∃ t ∈ ONSchreier.onT, t ^ 2 = x} ∧ x ^ 2 = 1}) ∧
    Nat.card (Subgroup.closure
      {x | x ∈ Subgroup.closure {x | ∃ t ∈ ONSchreier.onT, t ^ 2 = x} ∧ x ^ 2 = 1}) = 8 ∧
    ((Subgroup.closure
      {x | x ∈ Subgroup.closure {x | ∃ t ∈ ONSchreier.onT, t ^ 2 = x} ∧ x ^ 2 = 1}).subgroupOf
        ONSchreier.onT).Characteristic


end CFSG.ComponentClassification.UnbalancedCorr
