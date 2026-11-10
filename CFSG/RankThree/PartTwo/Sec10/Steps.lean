module

public import CFSG.RankThree.PartTwo.Sec10.Statements
public import CFSG.RankThree.PartTwo.Sec12.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Item103 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ g : G, g * c * g⁻¹ ∉ L

@[expose] def Item107 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ (d : G) (hd : d ∈ A), A ⊓ L = Subgroup.zpowers d →
      Sec12.transvectionGroup A ⟨d, hd⟩ ≤ Sec4.autIn ⊤ A

@[expose] def Item108 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G)

@[expose] def Item1012 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      ∃ a' : G, Sec10Std G A c L a' R ∧ ∃ U ∈ fourGroupsMinus A,
        U ≤ inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ((Subgroup.closure {a', d} : Subgroup G) : Set G))


theorem exists_inf_eq_zpowers (h97 : Sec9.Item97) {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {c : G} {L : Subgroup G} {a : G} {R : Subgroup G} (h : Sec9.Hyp91 G A c L a R) :
    ∃ d : G, A ⊓ L = Subgroup.zpowers d ∧ orderOf d = 3 ∧ A = Subgroup.closure {c, a, d} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h3, hcl⟩ := h97 G A c L a R h
  obtain ⟨d, hdL⟩ : ∃ d : G, A ⊓ L = Subgroup.zpowers d := by
    have hcyc : IsCyclic (A ⊓ L : Subgroup G) := isCyclic_of_prime_card h3
    obtain ⟨⟨d, hd⟩, hgen⟩ := hcyc.exists_generator
    refine ⟨d, le_antisymm ?_ (Subgroup.zpowers_le.mpr hd)⟩
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨y, hy⟩)
    have := congrArg Subtype.val hn
    simp only [Subgroup.coe_zpow] at this
    rw [← this]
    exact Subgroup.zpow_mem_zpowers d n
  exact ⟨d, hdL, by rw [← Nat.card_zpowers, ← hdL, h3], hcl d hdL⟩


end CFSG.RankThree.PartTwo.Sec10
