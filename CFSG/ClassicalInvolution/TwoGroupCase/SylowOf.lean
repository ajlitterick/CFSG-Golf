module

public import CFSG.ClassicalInvolution.TwoGroupCase.TightEmbedding

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

section SylowOf

variable [Finite G]

omit [Finite G] in
theorem IsSylow2Of.exists_sylow {P A : Subgroup G} (h : IsSylow2Of P A) :
    ∃ T : Sylow 2 A, (T : Subgroup A).map A.subtype = P := by
  have hP' : IsPGroup 2 (P.subgroupOf A) := h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm
  refine ⟨⟨P.subgroupOf A, hP', fun {Q} hQ hle => ?_⟩, Subgroup.map_subgroupOf_eq_of_le h.1⟩
  have h1 : IsPGroup 2 (Q.map A.subtype) := hQ.map A.subtype
  have h2 : P ≤ Q.map A.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
    exact Subgroup.map_mono hle
  have h3 := h.2.2 _ (Subgroup.map_subtype_le Q) h1 h2
  rw [← Subgroup.comap_map_eq_self_of_injective A.subtype_injective Q, h3]
  rfl

theorem IsSylow2Of.card_eq {P A : Subgroup G} (h : IsSylow2Of P A) :
    Nat.card P = 2 ^ (Nat.card A).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, rfl⟩ := h.exists_sylow
  rw [Nat.card_congr (Subgroup.equivMapOfInjective _ A.subtype A.subtype_injective).toEquiv.symm]
  exact T.card_eq_multiplicity

theorem card_le_of_isPGroup_le {P A : Subgroup G} (hP : IsPGroup 2 P) (hPA : P ≤ A) :
    Nat.card P ≤ 2 ^ (Nat.card A).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf A) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPA).symm
  obtain ⟨T, hT⟩ := hP'.exists_le_sylow
  have h1 : Nat.card (P.subgroupOf A) ≤ Nat.card T := Subgroup.card_le_of_le hT
  rw [T.card_eq_multiplicity] at h1
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv] at h1

theorem isSylow2Of_of_card {P A : Subgroup G} (hPA : P ≤ A) (hP : IsPGroup 2 P)
    (hc : 2 ^ (Nat.card A).factorization 2 ≤ Nat.card P) : IsSylow2Of P A :=
  ⟨hPA, hP, fun _ hP'A hP'2 hle =>
    (Subgroup.eq_of_le_of_card_ge hle ((card_le_of_isPGroup_le hP'2 hP'A).trans hc)).symm⟩

omit [Finite G] in
theorem exists_isSylow2Of_ge {P A : Subgroup G} (hP : IsPGroup 2 P) (hPA : P ≤ A) :
    ∃ P' : Subgroup G, IsSylow2Of P' A ∧ P ≤ P' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf A) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPA).symm
  obtain ⟨T, hT⟩ := hP'.exists_le_sylow
  refine ⟨(T : Subgroup A).map A.subtype, isSylow2Of_map_subtype T, ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hPA]
  exact Subgroup.map_mono hT

theorem IsSylow2Of.nonempty_mulEquiv {P Q A : Subgroup G} (hP : IsSylow2Of P A)
    (hQ : IsSylow2Of Q A) : Nonempty (P ≃* Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁, rfl⟩ := hP.exists_sylow
  obtain ⟨T₂, rfl⟩ := hQ.exists_sylow
  exact ⟨(Subgroup.equivMapOfInjective (T₁ : Subgroup A) A.subtype A.subtype_injective).symm.trans
    ((Sylow.equiv T₁ T₂).trans
      (Subgroup.equivMapOfInjective (T₂ : Subgroup A) A.subtype A.subtype_injective))⟩


end SylowOf

section Products

variable {M A B : Subgroup G}

theorem mul_injective_of_inf_eq_bot (hAB : A ⊓ B = ⊥) :
    Function.Injective (fun p : A × B => (p.1 : G) * p.2) := by
  intro p p' hpp
  have h1 : (p.1 : G) * p.2 = p'.1 * p'.2 := hpp
  have h2 : (p'.1 : G)⁻¹ * p.1 = p'.2 * (p.2 : G)⁻¹ := by
    calc (p'.1 : G)⁻¹ * p.1 = (p'.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
      _ = (p'.1 : G)⁻¹ * (p'.1 * p'.2) * (p.2 : G)⁻¹ := by rw [h1]
      _ = p'.2 * (p.2 : G)⁻¹ := by group
  have h3 : (p'.1 : G)⁻¹ * p.1 ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem p'.1.2) p.1.2, h2 ▸ B.mul_mem p'.2.2 (B.inv_mem p.2.2)⟩
  rw [hAB, Subgroup.mem_bot] at h3
  have h4 : p.1 = p'.1 := Subtype.ext (inv_mul_eq_one.mp h3).symm
  have h5 : (p.2 : G) = p'.2 := by
    have : (p.1 : G) * p.2 = p.1 * p'.2 := by rw [h1, ← h4]
    exact mul_left_cancel this
  exact Prod.ext h4 (Subtype.ext h5)

theorem natCard_eq_mul_of_inf_eq_bot (hA : A ≤ M) (hB : B ≤ M) (hAB : A ⊓ B = ⊥)
    (hM : ∀ m ∈ M, ∃ a ∈ A, ∃ b ∈ B, m = a * b) :
    Nat.card M = Nat.card A * Nat.card B := by
  let f : A × B → M := fun p => ⟨(p.1 : G) * p.2, M.mul_mem (hA p.1.2) (hB p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p p' hpp => mul_injective_of_inf_eq_bot hAB (congrArg Subtype.val hpp), ?_⟩
    rintro ⟨m, hm⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hM m hm
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf).symm, Nat.card_prod]

theorem exists_mul_of_natCard_eq [Finite G] (hA : A ≤ M) (hB : B ≤ M) (hAB : A ⊓ B = ⊥)
    (hcard : Nat.card M = Nat.card A * Nat.card B) : ∀ m ∈ M, ∃ a ∈ A, ∃ b ∈ B, m = a * b := by
  let f : A × B → M := fun p => ⟨(p.1 : G) * p.2, M.mul_mem (hA p.1.2) (hB p.2.2)⟩
  have hinj : Function.Injective f := fun p p' hpp =>
    mul_injective_of_inf_eq_bot hAB (congrArg Subtype.val hpp)
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hcard])
  intro m hm
  obtain ⟨p, hp⟩ := hbij.2 ⟨m, hm⟩
  exact ⟨p.1, p.1.2, p.2, p.2.2, (congrArg Subtype.val hp).symm⟩


theorem commute_of_mul_self_eq_one {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) * (x * y) = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  rw [mul_inv_rev, hx', hy'] at h1
  exact h1.symm


theorem le_normalizer_of_conj_mem {H T : Subgroup G} (hT : ∀ t ∈ T, ∀ u ∈ H, t * u * t⁻¹ ∈ H) :
    T ≤ Subgroup.normalizer (H : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨hT t ht u, fun hu => ?_⟩
  have h1 := hT t⁻¹ (T.inv_mem ht) _ hu
  have e : t⁻¹ * (t * u * t⁻¹) * t⁻¹⁻¹ = u := by group
  rwa [e] at h1

end Products

end CFSG.ClassicalInvolution
