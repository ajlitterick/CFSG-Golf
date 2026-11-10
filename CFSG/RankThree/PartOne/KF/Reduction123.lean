module

public import CFSG.RankThree.PartOne.S12.InputsEleven
public import CFSG.RankThree.PartOne.S12.InputsTable
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedLieAdmissible)
open scoped commutatorElement

@[expose] def KF123Classify : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    Table123Generic p L A₀ F → ∃ r : ℕ, 1 ≤ r ∧ r ≤ 12 ∧ r ≠ 11 ∧ RowModel p L r

@[expose] def KF123Row (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    Table123Generic p L A₀ F → RowModel p L r → RowData p L F r

@[expose] def KF123Row11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    Table123SU5 p L A₀ F → RowData p L F 11

theorem kf123_of_rows (hc : KF123Classify)
    (hrow : ∀ r : ℕ, 1 ≤ r → r ≤ 12 → r ≠ 11 → KF123Row r) (h11 : KF123Row11) : KF123 := by
  intro G _ _ p L A₀ F
  refine ⟨fun h => ?_, fun h => h11 G p L A₀ F h⟩
  obtain ⟨r, hr1, hr2, hr3, hmodel⟩ := hc G p L A₀ F h
  exact ⟨r, hr1, hr2, hr3, hrow r hr1 hr2 hr3 G p L A₀ F h hmodel⟩

@[expose] def KF123NTRow (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    Table123Generic p L A₀ F → RowModel p L r →
    ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) → ∀ hy : y ∈ Subgroup.normalizer (F : Set G),
      ¬ IsAutTransvection p F (F.normalizerMonoidHom ⟨y, hy⟩)

@[expose] def KF123NTRow11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    Table123SU5 p L A₀ F →
    ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) → ∀ hy : y ∈ Subgroup.normalizer (F : Set G),
      ¬ IsAutTransvection p F (F.normalizerMonoidHom ⟨y, hy⟩)

theorem kf123NoTransvection_of_rows (hc : KF123Classify)
    (hrow : ∀ r : ℕ, 1 ≤ r → r ≤ 12 → r ≠ 11 → KF123NTRow r) (h11 : KF123NTRow11) :
    KF123NoTransvection := by
  intro G _ _ p L A₀ F h y hy hyF
  rcases h with h | h
  · obtain ⟨r, hr1, hr2, hr3, hmodel⟩ := hc G p L A₀ F h
    exact hrow r hr1 hr2 hr3 G p L A₀ F h hmodel y hy hyF
  · exact h11 G p L A₀ F h y hy hyF


end CFSG.RankThree.PartOne
