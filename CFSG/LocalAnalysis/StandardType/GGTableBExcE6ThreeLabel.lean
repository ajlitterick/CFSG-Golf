module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGTableBE6LabelThree (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p = 3 ∧ (3 ∣ 2 ^ lab.n - 1 ∨ lab.n = 1)


theorem ggTableBE6LabelThree_of_split {p : ℕ} {lab : LargeEvenLabel} (htag : lab.tag = .E6)
    (hp3 : p = 3) (hs : LargeEvenSplit p lab) : GGTableBE6LabelThree p lab := by
  refine ⟨htag, hp3, ?_⟩
  rcases (largeEvenSplit_E_iff (Or.inl htag)).mp hs with h | h
  · exact Or.inl (hp3 ▸ h)
  · exact Or.inr h.1

@[expose] def GGE6ThreeEndNodeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    GGEndNode 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)


@[expose] def GGE6TwoEndNodeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → GGEndNodeElt 3 4 (adjointGroup .E6 K)

theorem TableBExc.E6Three.ggEndNode_E6_two_of_input (hT : GGE6TwoEndNodeInput) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGEndNode 3 4 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) :=
  ggEndNode_of_elt (TableBExc.E6Three.recipeID_subset_inn_E6_two hK)
    (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (TableBF4.ggEndNodeElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K) (hT K hK))

namespace TableBExc.E6Three

theorem recipeChevalleyE6_bstar_three {n : ℕ} (hn : 1 ≤ n) (h : 3 ∣ 2 ^ n - 1 ∨ n = 1)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false Q) :
    LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift 3 r R ∧ GGBstarBound 3 r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  rcases h with h3 | h1
  · have h3' : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
    exact ⟨5, ggTorusLift_E6_three h3', ggBstarBound_E6_three K hn hK h3'⟩
  · have hK2 : Nat.card K = 2 := by rw [hK, h1, pow_one]
    exact ⟨4, ggTorusLift_E6_two, ggBstarBound_E6_two hK2⟩

theorem recipeChevalleyE6_endNode_three (hE : GGE6ThreeEndNodeInput)
    (hT : GGE6TwoEndNodeInput) {n : ℕ} (h : 3 ∣ 2 ^ n - 1 ∨ n = 1)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false Q) :
    LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift 3 r R ∧ GGEndNode 3 r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  rcases h with h3 | h1
  · have h3' : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
    exact ⟨5, ggTorusLift_E6_three h3', hE K h3'⟩
  · have hK2 : Nat.card K = 2 := by rw [hK, h1, pow_one]
    exact ⟨4, ggTorusLift_E6_two, ggEndNode_E6_two_of_input hT hK2⟩

end TableBExc.E6Three

theorem largeEvenLabelAll_bstar_E6_three {lab : LargeEvenLabel} (htag : lab.tag = .E6)
    (hlab : LargeEvenInLambda2 lab) (h : 3 ∣ 2 ^ lab.n - 1 ∨ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧ GGBstarBound 3 r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  exact TableBExc.E6Three.recipeChevalleyE6_bstar_three hlab.1 h hQ

theorem ggBstarInputOn_E6_three : GGBstarInputOn GGTableBE6LabelThree :=
  TableBF4.ggBstarInputOn_of_labelAll fun _ _ _ hlab h => by
    obtain ⟨ht, rfl, h3⟩ := h
    exact largeEvenLabelAll_bstar_E6_three ht hlab h3

theorem ggStdSubPreInputOn_E6_three (hE : GGE6ThreeEndNodeInput) (hT : GGE6TwoEndNodeInput) :
    GGStdSubPreInputOn GGTableBE6LabelThree :=
  ggStdSubPreInputOn_of_labels fun _ lab _ _ h => by
    obtain ⟨ht, rfl, h3⟩ := h
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht h3
    subst ht
    intro Q hQ
    exact TableBExc.E6Three.recipeChevalleyE6_endNode_three hE hT h3 hQ


end CFSG.StandardType
