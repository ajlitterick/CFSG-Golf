module

public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.GroupTheory

open CFSG

variable {G : Type*} [Group G]

@[expose] def twoCoreX (B : Subgroup G) : Subgroup G :=
  ⨅ (b : G) (_ : b ∈ B) (_ : b ≠ 1), inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set G))

@[expose] def twoCoreJ (B : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
    ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set G)), B⁆

@[expose] def twoCoreAlpha (B : Subgroup G) : Subgroup G :=
  twoCoreJ B ⊔ twoCoreX B


theorem mem_twoCoreX_iff {B : Subgroup G} {x : G} :
    x ∈ twoCoreX B ↔
      ∀ b ∈ B, b ≠ 1 → x ∈ inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set G)) := by
  simp only [twoCoreX, Subgroup.mem_iInf]

theorem commutator_le_twoCoreJ {B : Subgroup G} {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set G)), B⁆ ≤ twoCoreJ B :=
  le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl)

theorem twoCoreJ_le_twoCoreAlpha (B : Subgroup G) : twoCoreJ B ≤ twoCoreAlpha B :=
  le_sup_left

theorem twoCoreX_le_twoCoreAlpha (B : Subgroup G) : twoCoreX B ≤ twoCoreAlpha B :=
  le_sup_right

end CFSG.RankThree.GroupTheory
