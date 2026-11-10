module

public import CFSG.Open.QuasithinDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.Timmesfeld.LocalTwoSubgroups

open CFSG.CGT.Timmesfeld75 CFSG.Assembly CFSG.Open Subgroup

variable {G : Type} [Group G]

def omega (i : ℕ) (B : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ B ∧ x ^ (2 ^ i) = 1}

def conjClass (A : Subgroup G) : Set (Subgroup G) :=
  {C | ∃ g : G, C = conjSubgroup g A}

def capSet (Sigma : Set (Subgroup G)) (U : Subgroup G) : Set (Subgroup G) :=
  {A | A ∈ Sigma ∧ A ≤ U}


def IsFStarEqTwoCore (M Q : Subgroup G) : Prop :=
  CFSG.Open.quasithinGenFitting M = Q ∧ (CFSG.pCore 2 M).map M.subtype = Q

structure IsAbelianNormalIn (M B : Subgroup G) : Prop where
  le : B ≤ M
  normal : (B.subgroupOf M).Normal
  abelian : IsMulCommutative B


structure HypothesisH (G : Type) [Group G] [Finite G] (M Q B : Subgroup G) : Prop where
  oTwo_trivial : CFSG.pCore 2 G = ⊥
  maxTwoLocal : rankThreeIsMaxTwoLocal M
  fStar : IsFStarEqTwoCore M Q
  abelianNormal : IsAbelianNormalIn M B
  ti : IsTI B


theorem HypothesisH.le [Finite G] {M Q B : Subgroup G} (h : HypothesisH G M Q B) : B ≤ M :=
  h.abelianNormal.le

namespace Section3

def B0 (B : Subgroup G) : Subgroup G := omega 1 B

def B1 (B : Subgroup G) : Subgroup G := omega 2 B

def Sigma (B : Subgroup G) : Set (Subgroup G) := conjClass (B0 B)


def A0 (A : Subgroup G) : Subgroup G := omega 1 A

def A1 (A : Subgroup G) : Subgroup G := omega 2 A


end Section3

namespace Section4


noncomputable def q (B : Subgroup G) : ℕ := Nat.card B

def Sigma (B : Subgroup G) : Set (Subgroup G) := conjClass B

def P (Q B : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ A ∈ capSet (Sigma B) Q, x ∈ A}

def T (Q B : Subgroup G) : Subgroup G := Q ⊓ centralizer (P Q B : Set G)


end Section4

end CFSG.Timmesfeld.LocalTwoSubgroups
