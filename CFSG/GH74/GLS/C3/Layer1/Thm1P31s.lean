module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Transport
public import CFSG.GH74.GLS.C3.Layer1.Thm1Leaves
public import CFSG.GH74.GLS.C3.Layer1.Thm1Quat
public import CFSG.GH74.GLS.C3.Layer1.Thm1AutA7

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1


end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

theorem exists_isElementaryAbelian_card_pRank {H : Type} [Group H] [Finite H] :
    ∃ A : Subgroup H, IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ pRank 2 H := by
  have hne : Set.Nonempty {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 ↥A ∧
      Nat.card ↥A = 2 ^ r} :=
    ⟨0, ⊥, Back.isElementaryAbelian_of_forall
      (fun u hu v hv => by rw [Subgroup.mem_bot.1 hu, Subgroup.mem_bot.1 hv])
      (fun u hu => by rw [Subgroup.mem_bot.1 hu, one_mul]), by simp⟩
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 ↥A ∧
      Nat.card ↥A = 2 ^ r} := by
    refine ⟨Nat.card H, ?_⟩
    rintro r ⟨B, -, hB⟩
    calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card H := Subgroup.card_le_card_group B
  exact Nat.sSup_mem hne hbdd

theorem exists_conj_le_of_isSylowOf {G : Type} [Group G] [Finite G] {P K X : Subgroup G}
    (hP : IsSylowOf 2 P K) (hXK : X ≤ K) (hX : IsPGroup 2 ↥X) :
    ∃ k ∈ K, ∀ y ∈ X, k⁻¹ * y * k ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', hQ'⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨c, c.2, fun y hy => ?_⟩
  have hy' : (⟨y, hXK hy⟩ : K) ∈ ((c • Q : Sylow 2 K) : Subgroup K) := hQ' hy
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  exact ⟨_, hy', by simp [MulAut.inv_apply]⟩

theorem exists_E₁ {G : Type} [Group G] [Finite G] {C T : Subgroup G} (hT : IsSylowOf 2 T C)
    (hrank : pRank 2 ↥C = 4) :
    ∃ E₁ : Subgroup G, E₁ ≤ T ∧ IsElementaryAbelian 2 ↥E₁ ∧ 16 ≤ Nat.card ↥E₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hcard⟩ := exists_isElementaryAbelian_card_pRank (H := ↥C)
  rw [hrank] at hcard
  have hE₀ : IsElementaryAbelian 2 ↥(A.map C.subtype) := by
    have := hA
    exact IsElementaryAbelian.map_subtype
  have hE₀card : Nat.card ↥(A.map C.subtype) = 16 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hcard]
    norm_num
  have hE₀p : IsPGroup 2 ↥(A.map C.subtype) := IsElementaryAbelian.isPGroup 2 _
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf hT (Subgroup.map_subtype_le A) hE₀p
  refine ⟨(A.map C.subtype).map (MulAut.conj c⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have := hc y hy
    simpa [MulAut.conj_apply] using this
  · have := hE₀
    exact IsElementaryAbelian.map _
  · rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hE₀card]


theorem quaternion_isMaximalClass (e : ℕ) (he : 1 ≤ e) :
    P34.IsMaximalClassTwoGroup (QuaternionGroup (2 ^ e)) := by
  obtain ⟨hcl, hcard⟩ := quaternionGroup_class e he
  have hp : IsPGroup 2 (QuaternionGroup (2 ^ e)) := IsPGroup.of_card hcard
  have : Group.IsNilpotent (QuaternionGroup (2 ^ e)) := hp.isNilpotent
  exact ⟨hp, this, by rw [hcl, hcard]⟩

theorem isMaximalClassTwoGroup_of_equiv {X Y : Type} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : P34.IsMaximalClassTwoGroup X) : P34.IsMaximalClassTwoGroup Y := by
  obtain ⟨hp, hnil, hcard⟩ := h
  refine ⟨hp.of_equiv e, ?_⟩
  have hnY : Group.IsNilpotent Y := Group.nilpotent_of_surjective e.toMonoidHom e.surjective
  have h1 : Group.nilpotencyClass Y ≤ Group.nilpotencyClass X :=
    Group.nilpotencyClass_le_of_surjective e.toMonoidHom e.surjective
  have h2 : Group.nilpotencyClass X ≤ Group.nilpotencyClass Y :=
    have := hnY
    Group.nilpotencyClass_le_of_surjective e.symm.toMonoidHom e.symm.surjective
  refine ⟨hnY, ?_⟩
  rw [← Nat.card_congr e.toEquiv, ← hcard, le_antisymm h1 h2]

theorem exists_Q_of_card_le_two {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hQ2 : ∀ A : Subgroup G, A ≤ M → IsElementaryAbelian 2 ↥A → Nat.card ↥A ≤ 2) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q M ∧ (IsCyclic ↥Q ∨ P34.IsMaximalClassTwoGroup ↥Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 M
  refine ⟨Q, hQ, ?_⟩
  have hrank : DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥Q := by
    intro u v huv
    by_contra hne
    have hu : orderOf (u : ↥Q) = 2 := u.2
    have hv : orderOf (v : ↥Q) = 2 := v.2
    obtain ⟨V, hVle, hV, hVcard⟩ :=
      LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute hu hv
        huv (fun h => hne (Subtype.ext h))
    have hVM : V.map Q.subtype ≤ M := by
      refine (Subgroup.map_subtype_le V).trans hQ.le
    have hVe : IsElementaryAbelian 2 ↥(V.map Q.subtype) := by
      have := hV
      exact IsElementaryAbelian.map_subtype
    have := hQ2 _ hVM hVe
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hVcard] at this
    omega
  rcases DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hQ.isPGroup hrank
    with hc | ⟨e, he, ⟨eq⟩⟩
  · exact Or.inl hc
  · exact Or.inr (isMaximalClassTwoGroup_of_equiv eq (quaternion_isMaximalClass e he))

end CFSG.GH74.GLS.C3.Layer1.Thm1
