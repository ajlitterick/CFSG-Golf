module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBA5Vertex
public import CFSG.GH74.E2.Cl2Rank
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FrattiniFaithful
public import CFSG.GH74.QTGen4.DSGen4.Leaf.RankBounds

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSBUQ2

variable {G : Type} [Group G]

theorem comm_mem_of_index_two {H : Subgroup G} (h : H.index = 2) (x y : G) : ⁅x, y⁆ ∈ H := by
  have hn : H.Normal := Subgroup.normal_of_index_eq_two h
  have h1 : x * y * x⁻¹ ∈ H ↔ y ∈ H := by
    constructor
    · intro hm
      have h2 := hn.conj_mem _ hm x⁻¹
      have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rw [e] at h2
      exact h2
    · intro hy
      exact hn.conj_mem _ hy x
  have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by rw [commutatorElement_def]
  rw [e, Subgroup.mul_mem_iff_of_index_two h, h1, Subgroup.inv_mem_iff]


theorem not_three_distinct {Φ : Subgroup G} (hΦ : Nat.card Φ = 2) {a b c : G} (ha : a ∈ Φ)
    (hb : b ∈ Φ) (hc : c ∈ Φ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  obtain ⟨u, v, -, huniv⟩ := Nat.card_eq_two_iff.mp hΦ
  have key : ∀ z : Φ, z = u ∨ z = v := by
    intro z
    have hz : z ∈ ({u, v} : Set Φ) := by
      rw [huniv]
      exact Set.mem_univ z
    simpa using hz
  have ha' := key ⟨a, ha⟩
  have hb' := key ⟨b, hb⟩
  have hc' := key ⟨c, hc⟩
  have hab' : (⟨a, ha⟩ : Φ) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
  have hac' : (⟨a, ha⟩ : Φ) ≠ ⟨c, hc⟩ := fun h => hac (congrArg Subtype.val h)
  have hbc' : (⟨b, hb⟩ : Φ) ≠ ⟨c, hc⟩ := fun h => hbc (congrArg Subtype.val h)
  rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2 <;> rcases hc' with h3 | h3
  all_goals first
    | exact hab' (h1.trans h2.symm)
    | exact hac' (h1.trans h3.symm)
    | exact hbc' (h2.trans h3.symm)


theorem mem_center_of_card_two {Φ : Subgroup G} (hΦ : Nat.card Φ = 2) {P : Subgroup G}
    (hP : P ≤ Subgroup.normalizer (Φ : Set G)) {x g : G} (hx : x ∈ Φ) (hg : g ∈ P) :
    g * x = x * g := by
  have hy : g * x * g⁻¹ ∈ Φ := (Subgroup.mem_normalizer_iff.mp (hP hg) x).mp hx
  by_cases hx1 : x = 1
  · subst hx1
    simp
  have hy1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have e : x = g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ := by group
    rw [h] at e
    simpa using e
  by_cases hxy : g * x * g⁻¹ = x
  · calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [hxy]
  · exfalso
    exact not_three_distinct hΦ (Subgroup.one_mem Φ) hx hy (Ne.symm hx1) (Ne.symm hy1)
      (fun h => hxy h.symm)


end DSBUQ2

open DSBUQ2


end CFSG.GH74.QTGen4.DSGen4
