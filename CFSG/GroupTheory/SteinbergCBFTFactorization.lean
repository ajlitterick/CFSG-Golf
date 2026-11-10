module

public import CFSG.GroupTheory.SteinbergCBFTGeneration

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup CFSG.HallHigman

section Factorization

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

open scoped Pointwise

@[expose] def IsFactorized (M N H : Subgroup G) : Prop :=
  (H : Set G) = ((H ⊓ M : Subgroup G) : Set G) * ((H ⊓ N : Subgroup G) : Set G)


omit [Finite G] hp in
theorem le_normalizer_map_subtype {R : Subgroup G} (T : Subgroup R) [T.Normal] :
    R ≤ normalizer ((T.map R.subtype : Subgroup G) : Set G) := by
  intro y hy
  have hmem : (⟨y, hy⟩ : R) ∈ normalizer (T : Set R) := by
    rw [normalizer_eq_top]
    exact mem_top _
  exact le_normalizer_map R.subtype ⟨⟨y, hy⟩, hmem, rfl⟩


theorem exists_sylow_normalized {W A : Subgroup G} (hA : IsPGroup p A)
    (hAW : A ≤ normalizer (W : Set G)) (hW : ¬ p ∣ Nat.card W) (q : ℕ) [Fact q.Prime] :
    ∃ S : Sylow q W, A ≤ normalizer (((S : Subgroup W).map W.subtype : Subgroup G) : Set G) := by
  let _ : MulDistribMulAction A W := Subgroup.conjMulDistribMulActionOfLeNormalizer A W hAW
  have hcard : ¬ p ∣ Nat.card (Sylow q W) := fun h =>
    hW (h.trans ((default : Sylow q W).card_dvd_index.trans (index_dvd_card _)))
  obtain ⟨S, hS⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q W) hcard
  refine ⟨S, fun a ha => mem_normalizer_iff.2 fun x => ?_⟩
  have hfix : (⟨a, ha⟩ : A) • (S : Subgroup W) = S := by
    rw [← Sylow.pointwise_smul_def]
    exact congrArg Sylow.toSubgroup (hS ⟨a, ha⟩)
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : (⟨a, ha⟩ : A) • s ∈ (S : Subgroup W) :=
      hfix ▸ Subgroup.smul_mem_pointwise_smul s _ _ hs
    exact ⟨_, hs', rfl⟩
  · rintro ⟨s', hs', hs'x⟩
    rw [← hfix] at hs'
    obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hs'
    refine ⟨s, hs, ?_⟩
    have h1 : a * (s : G) * a⁻¹ = a * x * a⁻¹ := hs'x
    simpa using h1

omit hp in
theorem lt_inf_normalizer_of_lt {q : ℕ} [Fact q.Prime] {Q S : Subgroup G} (hS : IsPGroup q S)
    (hQS : Q < S) : Q < S ⊓ normalizer (Q : Set G) := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : Q.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hQS.ne (le_antisymm hQS.le (subgroupOf_eq_top.1 h))
  obtain ⟨x, hxN, hxQ⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq hQS.le] at hxN
  refine lt_of_le_of_ne (le_inf hQS.le le_normalizer) fun h => hxQ ?_
  have hx : (x : G) ∈ S ⊓ normalizer (Q : Set G) := mem_inf.2 ⟨x.2, hxN⟩
  rw [← h] at hx
  exact hx

theorem exists_sylow_ge_normalized {q : ℕ} [Fact q.Prime] {W A Q₁ : Subgroup G}
    (hA : IsPGroup p A) (hAW : A ≤ normalizer (W : Set G)) (hW : ¬ p ∣ Nat.card W)
    (hQ₁W : Q₁ ≤ W) (hQ₁ : IsPGroup q Q₁) (hAQ₁ : A ≤ normalizer (Q₁ : Set G)) :
    ∃ Q₂ : Subgroup G, Q₁ ≤ Q₂ ∧ Q₂ ≤ W ∧ IsPGroup q Q₂ ∧ A ≤ normalizer (Q₂ : Set G) ∧
      ¬ q ∣ Q₂.relIndex W := by
  let 𝒯 : Set (Subgroup G) := {Q | Q₁ ≤ Q ∧ Q ≤ W ∧ IsPGroup q Q ∧ A ≤ normalizer (Q : Set G)}
  obtain ⟨Q₂, -, hmax⟩ := 𝒯.toFinite.exists_le_maximal (show Q₁ ∈ 𝒯 from ⟨le_rfl, hQ₁W, hQ₁, hAQ₁⟩)
  obtain ⟨hQ₁₂, hQ₂W, hQ₂, hAQ₂⟩ := hmax.prop
  refine ⟨Q₂, hQ₁₂, hQ₂W, hQ₂, hAQ₂, ?_⟩
  set W' := W ⊓ normalizer (Q₂ : Set G) with hW'def
  have hAW' : A ≤ normalizer (W' : Set G) :=
    le_normalizer_inf_of_le hAW (hAQ₂.trans le_normalizer)
  have hW' : ¬ p ∣ Nat.card W' := fun h => hW (h.trans (card_dvd_of_le inf_le_left))
  obtain ⟨S', hS'⟩ := exists_sylow_normalized hA hAW' hW' q
  have hQ₂W' : Q₂ ≤ W' := le_inf hQ₂W le_normalizer
  have hQ₂S' : Q₂ ≤ (S' : Subgroup W').map W'.subtype := by
    have hn : (Q₂.subgroupOf W').Normal := normal_subgroupOf_of_le_normalizer inf_le_right
    have hQ₂p' : IsPGroup q (Q₂.subgroupOf W') := hQ₂.comap_subtype
    have hle : Q₂.subgroupOf W' ≤ S' := hQ₂p'.le_sylow_of_normal S'
    have h2 : (Q₂.subgroupOf W').map W'.subtype = Q₂ := by
      rw [subgroupOf_map_subtype, inf_eq_left.2 hQ₂W']
    calc Q₂ = (Q₂.subgroupOf W').map W'.subtype := h2.symm
      _ ≤ _ := map_mono hle
  have hS'T : (S' : Subgroup W').map W'.subtype ∈ 𝒯 :=
    ⟨hQ₁₂.trans hQ₂S', (map_subtype_le _).trans inf_le_left, S'.isPGroup'.map _, hS'⟩
  have heq : (S' : Subgroup W').map W'.subtype = Q₂ :=
    le_antisymm (hmax.le_of_ge hS'T hQ₂S') hQ₂S'
  have hsyl : ¬ q ∣ Q₂.relIndex W' := by
    have h3 : ((S' : Subgroup W').map W'.subtype).subgroupOf W' = S' :=
      comap_map_eq_self_of_injective W'.subtype_injective _
    rw [← heq, relIndex, h3]
    exact S'.not_dvd_index
  obtain ⟨S₀, hS₀⟩ := (hQ₂.comap_subtype (K := W)).exists_le_sylow
  have hQ₂S : Q₂ ≤ (S₀ : Subgroup W).map W.subtype := by
    have h2 : (Q₂.subgroupOf W).map W.subtype = Q₂ := by
      rw [subgroupOf_map_subtype, inf_eq_left.2 hQ₂W]
    calc Q₂ = (Q₂.subgroupOf W).map W.subtype := h2.symm
      _ ≤ _ := map_mono hS₀
  have hSp : IsPGroup q ↥((S₀ : Subgroup W).map W.subtype) := S₀.isPGroup'.map _
  have hSN : (S₀ : Subgroup W).map W.subtype ⊓ normalizer (Q₂ : Set G) ≤ Q₂ :=
    le_of_isPGroup_of_not_dvd_relIndex hQ₂ hQ₂W' hsyl (hSp.to_le inf_le_left)
      (inf_le_inf_right _ (map_subtype_le _)) inf_le_right
  have hQ₂eq : Q₂ = (S₀ : Subgroup W).map W.subtype := by
    by_contra hne
    exact (lt_irrefl Q₂) ((lt_inf_normalizer_of_lt hSp (lt_of_le_of_ne hQ₂S hne)).trans_le hSN)
  have h4 : ((S₀ : Subgroup W).map W.subtype).subgroupOf W = S₀ :=
    comap_map_eq_self_of_injective W.subtype_injective _
  rw [hQ₂eq, relIndex, h4]
  exact S₀.not_dvd_index

omit [Finite G] hp in
theorem card_setMul_mul_card_inf (A B : Subgroup G) :
    Nat.card ↥((A : Set G) * (B : Set G)) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient B (A : Set G)
  have himg : Nat.card ↥((A : Set G).image ((↑) : G → G ⧸ B)) = B.relIndex A := by
    have horb : MulAction.orbit ↥A ((1 : G) : G ⧸ B) = (A : Set G).image ((↑) : G → G ⧸ B) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(a : G), a.2, by simp [Subgroup.smul_def]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, by simp [Subgroup.smul_def]⟩
    have hstab : MulAction.stabilizer ↥A ((1 : G) : G ⧸ B) = B.subgroupOf A := by
      ext a
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have : (a • ((1 : G) : G ⧸ B)) = ((a : G) : G ⧸ B) := by
        simp [Subgroup.smul_def]
      rw [this, QuotientGroup.eq]
      constructor
      · intro h
        simpa using B.inv_mem h
      · intro h
        simpa using B.inv_mem h
    have := MulAction.index_stabilizer ↥A ((1 : G) : G ⧸ B)
    rw [hstab] at this
    rw [← horb, Nat.card_coe_set_eq, ← this]
    rfl
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_comm B A] at h2
  rw [h1, himg]
  calc Nat.card ↥B * B.relIndex A * Nat.card ↥(A ⊓ B)
      = Nat.card ↥B * (B.relIndex A * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h2]; ring

omit [Finite G] hp in
theorem card_mul_card_inf_of_isFactorized {M N R : Subgroup G} (h : IsFactorized M N R) :
    Nat.card R * Nat.card ↥(R ⊓ M ⊓ N) = Nat.card ↥(R ⊓ M) * Nat.card ↥(R ⊓ N) := by
  have h1 := card_setMul_mul_card_inf (R ⊓ M) (R ⊓ N)
  rw [← inf_inf_distrib_left, ← inf_assoc] at h1
  have h2 : Nat.card ↥(((R ⊓ M : Subgroup G) : Set G) * ((R ⊓ N : Subgroup G) : Set G)) =
      Nat.card R := by
    rw [← h]
    rfl
  rw [h2] at h1
  exact h1

omit hp in
theorem card_eq_card_map_mul_card_inf {X' : Type*} [Group X'] (f : G →* X') (H : Subgroup G) :
    Nat.card H = Nat.card (H.map f) * Nat.card ↥(f.ker ⊓ H) := by
  rw [CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex (inf_le_right : f.ker ⊓ H ≤ H),
    inf_relIndex_right, relIndex_ker, mul_comm]


omit hp in
theorem factorization_eq_of_not_dvd_relIndex {q : ℕ} {H K : Subgroup G}
    (h : H ≤ K) (hn : ¬ q ∣ H.relIndex K) :
    (Nat.card K).factorization q = (Nat.card H).factorization q := by
  have hr : H.relIndex K ≠ 0 := index_ne_zero_of_finite
  rw [CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex h,
    Nat.factorization_mul Nat.card_pos.ne' hr, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hn, add_zero]


end Factorization

end CFSG.GroupTheory.FT63ChII
