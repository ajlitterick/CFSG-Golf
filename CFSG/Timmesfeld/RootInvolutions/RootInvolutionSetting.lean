module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.Timmesfeld.RootInvolutions

open CFSG.CGT.Timmesfeld75 CFSG.Assembly Subgroup

open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def normalizerIn (A B : Subgroup G) : Subgroup G := A ⊓ normalizer (B : Set G)

def IsRootTypeIn (p : ℕ) (H A : Subgroup G) : Prop :=
  A ≤ H ∧ IsElemAbelian p A ∧
    (∀ h ∈ H, A ⊓ conjSubgroup h A = A ∨ A ⊓ conjSubgroup h A = ⊥) ∧
    (∀ h ∈ H, normalizerIn A (conjSubgroup h A) ≠ ⊥ →
      ∀ a ∈ A, ∀ b ∈ conjSubgroup h A, a * b = b * a)

def IsRootType (p : ℕ) (A : Subgroup G) : Prop := IsRootTypeIn p ⊤ A


def zStar (G : Type) [Group G] : Subgroup G :=
  (Subgroup.center (G ⧸ oddCore G)).comap (QuotientGroup.mk' (oddCore G))


def weakClosure (A C : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ g : G, conjSubgroup g A ≤ C ∧ x ∈ conjSubgroup g A}


structure ElementaryAbelianTIRootCentralizerHypothesis (A : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 A
  ti : IsTI A
  sylow : ∃ S : Subgroup G, IsPGroup 2 S ∧ (∀ T : Subgroup G, IsPGroup 2 T → S ≤ T → T = S) ∧
    S ≤ normalizer (A : Set G)
  rootTypeInCentralizer : ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) →
    IsRootTypeIn 2 (centralizer (A : Set G)) (conjSubgroup g A)

structure ElementaryAbelianTIWeakClosureHypothesis (A : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 A
  ti : IsTI A
  derived_le : ⁅weakClosure A (centralizer (A : Set G)), weakClosure A (centralizer (A : Set G))⁆ ≤ A
  sylow : ∃ S : Subgroup G, IsPGroup 2 S ∧ (∀ T : Subgroup G, IsPGroup 2 T → S ≤ T → T = S) ∧
    S ≤ normalizer (A : Set G)


namespace Section3


def IsChoice (A Abar : Subgroup G) : Prop :=
  (∃ g : G, Abar = conjSubgroup g A) ∧
  (normalizerIn Abar A ≠ ⊥ ∧ normalizerIn Abar A ≠ Abar) ∧
  ∀ g : G, (normalizerIn (conjSubgroup g A) A ≠ ⊥ ∧
      normalizerIn (conjSubgroup g A) A ≠ conjSubgroup g A) →
    Nat.card (normalizerIn (conjSubgroup g A) A) ≤ Nat.card (normalizerIn Abar A)

@[expose] def A0 (A Abar : Subgroup G) : Subgroup G := normalizerIn A Abar

@[expose] def Abar0 (A Abar : Subgroup G) : Subgroup G := normalizerIn Abar A

@[expose] def M (A Abar : Subgroup G) : Subgroup G := A0 A Abar ⊔ Abar0 A Abar

@[expose] def X (A Abar : Subgroup G) : Subgroup G := A ⊔ Abar

@[expose] noncomputable def q (A Abar : Subgroup G) : ℕ := (Abar0 A Abar).relIndex Abar

@[expose] def Y (A Abar : Subgroup G) (s : G) : Subgroup G := A ⊔ Abar ⊔ conjSubgroup s Abar

@[expose] def N (A Abar : Subgroup G) (s : G) : Subgroup G :=
  A0 A Abar ⊔ Abar0 A Abar ⊔ conjSubgroup s (Abar0 A Abar)

structure Notation (A Abar S₀ B : Subgroup G) : Prop where
  choice : IsChoice A Abar
  sylow : IsPGroup 2 S₀ ∧ S₀ ≤ normalizer (A : Set G) ∧
    (∀ T : Subgroup G, IsPGroup 2 T → T ≤ normalizer (A : Set G) → S₀ ≤ T → T = S₀)
  contains : A ⊔ Abar0 A Abar ≤ S₀
  conj : ∃ g : G, B = conjSubgroup g A
  ne : B ≠ A
  le : B ≤ S₀ ⊓ centralizer (A : Set G)

def IsSChoice (A Abar S₀ B : Subgroup G) (s : G) : Prop :=
  ∃ b ∈ B, b ≠ 1 ∧
    ((∃ x ∈ Abar0 A Abar, x ≠ 1 ∧ (orderOf (x * b) = 2 ∨ orderOf (x * b) = 4)) ∧ s = b ∨
     ((∀ x ∈ Abar0 A Abar, x ≠ 1 → orderOf (x * b) ≠ 2 ∧ orderOf (x * b) ≠ 4) ∧
      ∃ x ∈ Abar0 A Abar, x ≠ 1 ∧
        s ∈ Subgroup.closure {x, b} ∧ s ∈ S₀ ∧ s ∈ centralizer (A : Set G) ∧
        Abar0 A Abar ≠ conjSubgroup s (Abar0 A Abar) ∧
        (∀ a ∈ Abar0 A Abar, ∀ c ∈ conjSubgroup s (Abar0 A Abar), a * c = c * a) ∧
        orderOf s = 4))

end Section3

namespace Section4

def D (A Abar : Subgroup G) (s : G) : Set G :=
  {t | ∃ y ∈ Section3.Y A Abar s, ∃ a ∈ A, a ∉ Section3.A0 A Abar ∧ t = y * a * y⁻¹}


end Section4

namespace Section5

def H (A Abar : Subgroup G) : Subgroup G :=
  weakClosure (Section3.A0 A Abar) (normalizer (A : Set G))


end Section5

end CFSG.Timmesfeld.RootInvolutions
