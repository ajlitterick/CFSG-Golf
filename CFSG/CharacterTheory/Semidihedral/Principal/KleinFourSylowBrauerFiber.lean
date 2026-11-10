module

public import CFSG.CharacterTheory.Semidihedral.Principal.OrderEightFourGroupDefectParity
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralLinearBlockAssociates

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.BlockOrbits

namespace KleinFourFiber

variable {G : Type*} [Group G]

theorem mem_centralizer_subgroupOf_iff {S C : Subgroup G} (hSC : S ≤ C) (x : C) :
    x ∈ Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C) ↔
      (x : G) ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    exact congrArg Subtype.val (h ⟨g, hSC hg⟩ (Subgroup.mem_subgroupOf.mpr hg))
  · intro h y hy
    exact Subtype.ext (h y (Subgroup.mem_subgroupOf.mp hy))

@[expose] def centralizerSubgroupOfEquiv {S C : Subgroup G} (hSC : S ≤ C)
    (hWC : Subgroup.centralizer (S : Set G) ≤ C) :
    Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C) ≃*
      Subgroup.centralizer (S : Set G) where
  toFun x := ⟨((x : C) : G), (mem_centralizer_subgroupOf_iff hSC x).mp x.2⟩
  invFun w := ⟨⟨w, hWC w.2⟩, (mem_centralizer_subgroupOf_iff hSC _).mpr w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl


@[expose] def fiberConj {S C : Subgroup G} (hSC : S ≤ C)
    (hWC : Subgroup.centralizer (S : Set G) ≤ C) (n : G)
    (hn : n ∈ Subgroup.normalizer (S : Set G)) :
    Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C) ≃*
      Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C) :=
  ((centralizerSubgroupOfEquiv hSC hWC).trans (centralizerConjugation S n hn)).trans
    (centralizerSubgroupOfEquiv hSC hWC).symm

theorem fiberConj_apply {S C : Subgroup G} (hSC : S ≤ C)
    (hWC : Subgroup.centralizer (S : Set G) ≤ C) (n : G)
    (hn : n ∈ Subgroup.normalizer (S : Set G))
    (x : Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) :
    (((fiberConj hSC hWC n hn x : Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) :
      C) : G) = n * ((x : C) : G) * n⁻¹ := rfl


theorem mem_normalizer_of_subgroupOf {S C : Subgroup G} (hSC : S ≤ C) (c : C)
    (hc : c ∈ Subgroup.normalizer ((S.subgroupOf C : Subgroup C) : Set C)) :
    (c : G) ∈ Subgroup.normalizer (S : Set G) := by
  have hnorm := Subgroup.mem_normalizer_iff.mp hc
  have hfwd : ∀ g ∈ S, (c : G) * g * (c : G)⁻¹ ∈ S := by
    intro g hg
    have h := (hnorm ⟨g, hSC hg⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
    exact Subgroup.mem_subgroupOf.mp h
  have hbwd : ∀ g ∈ S, (c : G)⁻¹ * g * c ∈ S := by
    intro g hg
    have hmem : (c⁻¹ * ⟨g, hSC hg⟩ * c : C) ∈ S.subgroupOf C := by
      apply (hnorm _).mpr
      have hval : c * (c⁻¹ * ⟨g, hSC hg⟩ * c) * c⁻¹ = ⟨g, hSC hg⟩ := by group
      rw [hval]
      exact Subgroup.mem_subgroupOf.mpr hg
    exact Subgroup.mem_subgroupOf.mp hmem
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact hfwd g
  · intro h
    have := hbwd _ h
    simpa [mul_assoc] using this

theorem sq_mem_centralizer {S : Subgroup G} (hS : IsKleinFour S) {t : G} (htS : t ∈ S)
    (ht1 : t ≠ 1) {c : G} (hcN : c ∈ Subgroup.normalizer (S : Set G)) (hct : c * t = t * c) :
    c * c ∈ Subgroup.centralizer (S : Set G) := by
  have : IsKleinFour S := hS
  have hnorm := Subgroup.mem_normalizer_iff.mp hcN
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hconjt : c * t * c⁻¹ = t := by rw [hct]; group
  have hcs : c * s * c⁻¹ ∈ S := (hnorm s).mp hs
  have hfix_or_swap : c * s * c⁻¹ = s ∨ c * s * c⁻¹ = t * s := by
    by_cases hs1 : s = 1
    · left
      rw [hs1]
      group
    by_cases hst : s = t
    · left
      rw [hst, hconjt]
    by_cases heq : c * s * c⁻¹ = s
    · exact Or.inl heq
    · right
      have h1 : (⟨c * s * c⁻¹, hcs⟩ : S) ≠ 1 := fun h => hs1 (by
        have hval : c * s * c⁻¹ = 1 := congrArg Subtype.val h
        exact conj_eq_one_iff.mp hval)
      have h2 : (⟨c * s * c⁻¹, hcs⟩ : S) ≠ ⟨t, htS⟩ := fun h => hst (by
        have hval : c * s * c⁻¹ = t := congrArg Subtype.val h
        rw [← hconjt] at hval
        exact mul_left_cancel (mul_right_cancel hval))
      have h3 : (⟨c * s * c⁻¹, hcs⟩ : S) ≠ ⟨s, hs⟩ := fun h => heq (congrArg Subtype.val h)
      have ht' : (⟨t, htS⟩ : S) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
      have hs' : (⟨s, hs⟩ : S) ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
      have hts : (⟨t, htS⟩ : S) ≠ ⟨s, hs⟩ := fun h => hst (congrArg Subtype.val h).symm
      have hmul := IsKleinFour.eq_mul_of_ne_all ht' hs' hts h1 h2 h3
      exact congrArg Subtype.val hmul
  have htt : t * t = 1 := by
    have h := IsKleinFour.mul_self (⟨t, htS⟩ : S)
    exact congrArg Subtype.val h
  have hc2 : c * c * s * (c * c)⁻¹ = s := by
    rcases hfix_or_swap with h | h
    · calc c * c * s * (c * c)⁻¹ = c * (c * s * c⁻¹) * c⁻¹ := by group
        _ = s := by rw [h, h]
    · calc c * c * s * (c * c)⁻¹ = c * (c * s * c⁻¹) * c⁻¹ := by group
        _ = c * (t * s) * c⁻¹ := by rw [h]
        _ = (c * t * c⁻¹) * (c * s * c⁻¹) := by group
        _ = t * (t * s) := by rw [hconjt, h]
        _ = s := by rw [← mul_assoc, htt, one_mul]
  calc s * (c * c) = c * c * s * (c * c)⁻¹ * (c * c) := by rw [hc2]
    _ = c * c * s := by group

theorem kleinFour_comm {S : Subgroup G} (hS : IsKleinFour S) :
    ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
  intro a ha b hb
  have : IsKleinFour S := hS
  exact congrArg Subtype.val
    ((IsKleinFour.isMulCommutative (G := S)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem isKleinFour_subgroupOf {S K : Subgroup G} (hS : IsKleinFour S) (hSK : S ≤ K) :
    IsKleinFour (S.subgroupOf K) where
  card_four := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]
    exact hS.card_four
  exponent_two := by
    rw [Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSK)]
    exact hS.exponent_two

variable [Finite G]

omit [Finite G] in
theorem centralizer_subgroupOf_normalizer_normal (S : Subgroup G) :
    ((Subgroup.centralizer (S : Set G)).subgroupOf (Subgroup.normalizer (S : Set G))).Normal := by
  constructor
  intro w hw n
  rw [Subgroup.mem_subgroupOf] at hw ⊢
  change (n : G) * w * (n : G)⁻¹ ∈ Subgroup.centralizer (S : Set G)
  exact (centralizer_conjugation_mem_iff S n w n.property).mpr hw

theorem odd_index_centralizer (S : Sylow 2 G)
    (hSab : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * b = b * a) :
    Odd ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index := by
  have hSW : (S : Subgroup G) ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
    OrbitIdempotents.le_centralizer_self_of_comm _ hSab
  have hle : (S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G)) ≤
      (Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hSW (Subgroup.mem_subgroupOf.mp hx))
  have hSylow := Sylow.not_dvd_index (S.subtype (Subgroup.le_normalizer))
  rw [Sylow.coe_subtype] at hSylow
  refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => hSylow ?_)
  exact h.trans (Subgroup.index_dvd_of_le hle)


theorem mem_centralizer_of_fix (S : Sylow 2 G) (hS : IsKleinFour (S : Subgroup G)) {t : G}
    (htS : t ∈ (S : Subgroup G)) (ht1 : t ≠ 1) {c : G}
    (hcN : c ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (hct : c * t = t * c) :
    c ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  have hc2 := sq_mem_centralizer hS htS ht1 hcN hct
  have : ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).Normal :=
    centralizer_subgroupOf_normalizer_normal _
  have hk := Subgroup.pow_index_mem ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
    (Subgroup.normalizer ((S : Subgroup G) : Set G))) ⟨c, hcN⟩
  rw [Subgroup.mem_subgroupOf] at hk
  obtain ⟨j, hj⟩ := odd_index_centralizer S (kleinFour_comm hS)
  set k := ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
    (Subgroup.normalizer ((S : Subgroup G) : Set G))).index with hkdef
  have hck : c ^ k ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := hk
  have hc : c = ((c * c) ^ j)⁻¹ * c ^ k := by
    rw [hj, ← sq, ← pow_mul, pow_succ]
    group
  rw [hc]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hc2 j)) hck

omit [Finite G] in
theorem normalizer_zpowers_le {t : G} (ht1 : t ≠ 1) (htt : t * t = 1) :
    Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  intro g hg
  apply DihedralAssociates.mem_centralizer_zpowers_of_commute
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two, htt]) ht1
  have hmem : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
    (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat] at hk
  have hconj : g * t * g⁻¹ = t := by
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hk
      exact absurd (conj_eq_one_iff.mp hk.symm) ht1
    · rw [h1, zpow_one] at hk
      exact hk.symm
  calc g * t = (g * t * g⁻¹) * g := by group
    _ = t * g := by rw [hconj]


variable [Fintype G]

omit [Finite G] in
theorem brauerProjection_composite (ring : Subring ℂ) (P S C : Subgroup G) (hPS : P ≤ S)
    (hCP : Subgroup.centralizer (P : Set G) ≤ C) (hCN : C ≤ Subgroup.normalizer (P : Set G))
    (hSC : S ≤ C) (hWC : Subgroup.centralizer (S : Set G) ≤ C)
    (z : centralCoefficientSubring (G := G) ring) :
    centralCoefficientTransport ring (centralizerSubgroupOfEquiv hSC hWC)
        (centralNormalizerCoefficientProjection ring (S.subgroupOf C)
          (Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) le_rfl
          (Subgroup.centralizer_le_normalizer _)
          (centralNormalizerCoefficientProjection ring P C hCP hCN z)) =
      centralNormalizerCoefficientProjection ring S (Subgroup.centralizer (S : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) z := by
  apply Subtype.ext
  ext w
  have hwP : (w : G) ∈ Subgroup.centralizer (P : Set G) := Subgroup.centralizer_le hPS w.property
  rw [centralCoefficientTransport_coeff, centralNormalizerCoefficientProjection_coeff,
    centralNormalizerCoefficientProjection_coeff, centralNormalizerCoefficientProjection_coeff,
    ite_eq_left ((centralizerSubgroupOfEquiv hSC hWC).symm w).property, ite_eq_left w.property]
  split_ifs with h
  · rfl
  · exact absurd hwP h

omit [Finite G] in
theorem brauer_composite (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ)
    [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (P S C : Subgroup G)
    (hP : IsPGroup p P) (hSp : IsPGroup p S) (hPS : P ≤ S)
    (hCP : Subgroup.centralizer (P : Set G) ≤ C) (hCN : C ≤ Subgroup.normalizer (P : Set G))
    (hSC : S ≤ C) (hWC : Subgroup.centralizer (S : Set G) ≤ C)
    (cb : FiniteIrreducibleCharacterBasis C)
    (wb : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)))
    (gb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (S : Set G)))
    {γ : wb.index} {γG : gb.index}
    (hγ : LabelTransport wb gb (centralizerSubgroupOfEquiv hSC hWC) γ γG) {c : cb.index}
    (hc : brauerNormalizerCharacterResidueHom ideal p (S.subgroupOf C) hSp.comap_subtype
      (Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) le_rfl
      (Subgroup.centralizer_le_normalizer _) wb γ = centralCharacterResidueHom cb ideal c) :
    brauerNormalizerCharacterResidueHom ideal p P hP C hCP hCN cb c =
      brauerNormalizerCharacterResidueHom ideal p S hSp (Subgroup.centralizer (S : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) gb γG := by
  apply RingHom.ext
  intro z
  change centralCharacterResidueHom cb ideal c (centralNormalizerCoefficientProjection _ P C hCP hCN
    z) = centralCharacterResidueHom gb ideal γG (centralNormalizerCoefficientProjection _ S _ le_rfl
      (Subgroup.centralizer_le_normalizer _) z)
  rw [← hc, ← brauerProjection_composite _ P S C hPS hCP hCN hSC hWC z,
    centralCharacterResidueHom_labelTransport wb gb ideal _ hγ]
  rfl

omit [Finite G] in
theorem brauer_eq_of_same {K : Type*} [Group K] [Fintype K]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (P : Subgroup K) (hP : IsPGroup p P)
    (L : Subgroup K) (hCL : Subgroup.centralizer (P : Set K) ≤ L)
    (hLN : L ≤ Subgroup.normalizer (P : Set K)) (lb : FiniteIrreducibleCharacterBasis L)
    {γ₁ γ₂ : lb.index} (hsame : sameCoefficientBlock lb (localizedComplexIntegerRing ideal) γ₁ γ₂) :
    brauerNormalizerCharacterResidueHom ideal p P hP L hCL hLN lb γ₁ =
      brauerNormalizerCharacterResidueHom ideal p P hP L hCL hLN lb γ₂ := by
  apply RingHom.ext
  intro z
  change centralCharacterResidueHom lb ideal γ₁ _ = centralCharacterResidueHom lb ideal γ₂ _
  rw [(sameCoefficientBlock_iff_centralCharacterResidueHom_eq lb ideal γ₁ γ₂).mp hsame]


omit [Finite G] [Fintype G] in
theorem le_centralizer_zpowers {S : Subgroup G} (hS : IsKleinFour S) {t : G} (htS : t ∈ S) :
    S ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := fun y hy =>
  DihedralAssociates.mem_centralizer_zpowers_of_commute (kleinFour_comm hS y hy t htS)


omit [Finite G] [Fintype G] in
theorem coefficientBlock_eq_iff {K : Type*} [Group K] [Fintype K]
    (basis : FiniteIrreducibleCharacterBasis K) (ring : Subring ℂ) (χ ψ : basis.index) :
    coefficientBlock basis ring χ = coefficientBlock basis ring ψ ↔
      sameCoefficientBlock basis ring χ ψ := by
  constructor
  · intro h
    rw [← coefficientBlock_mem_iff, h]
    exact coefficientBlock_self_mem _ _ _
  · intro h
    exact (coefficientBlock_eq_of_mem basis ring ((coefficientBlock_mem_iff _ _ _ _).mpr h)).symm


section Action

variable {S C : Subgroup G} (hSC : S ≤ C) (hWC : Subgroup.centralizer (S : Set G) ≤ C)
  (wb : FiniteIrreducibleCharacterBasis
    (Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)))

omit [Finite G] [Fintype G] in
theorem fiberConj_mul (n m : Subgroup.normalizer (S : Set G))
    (x : Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) :
    fiberConj hSC hWC ((n * m : Subgroup.normalizer (S : Set G)) : G) (n * m).2 x =
      fiberConj hSC hWC n n.2 (fiberConj hSC hWC m m.2 x) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [fiberConj_apply, fiberConj_apply, fiberConj_apply, Subgroup.coe_mul]
  group

omit [Finite G] [Fintype G] in
theorem fiberConj_one (x : Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) :
    fiberConj hSC hWC ((1 : Subgroup.normalizer (S : Set G)) : G)
      (1 : Subgroup.normalizer (S : Set G)).2 x = x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [fiberConj_apply, Subgroup.coe_one]
  group

@[expose] noncomputable def fiberLabel (n : Subgroup.normalizer (S : Set G)) (γ : wb.index) :
    wb.index :=
  (labelTransport_exists wb wb (fiberConj hSC hWC n n.2) γ).choose

omit [Finite G] in
theorem fiberLabel_spec (n : Subgroup.normalizer (S : Set G)) (γ : wb.index) :
    LabelTransport wb wb (fiberConj hSC hWC n n.2) γ (fiberLabel hSC hWC wb n γ) :=
  (labelTransport_exists wb wb (fiberConj hSC hWC n n.2) γ).choose_spec

omit [Finite G] in
theorem fiberLabel_one (γ : wb.index) : fiberLabel hSC hWC wb 1 γ = γ :=
  labelTransport_unique (fiberLabel_spec hSC hWC wb 1 γ) (fun x => by rw [fiberConj_one])

omit [Finite G] in
theorem fiberLabel_mul (n m : Subgroup.normalizer (S : Set G)) (γ : wb.index) :
    fiberLabel hSC hWC wb (n * m) γ = fiberLabel hSC hWC wb n (fiberLabel hSC hWC wb m γ) :=
  labelTransport_unique (fiberLabel_spec hSC hWC wb (n * m) γ) (fun x => by
    rw [fiberConj_mul]
    exact (fiberLabel_spec hSC hWC wb n (fiberLabel hSC hWC wb m γ) _).trans
      (fiberLabel_spec hSC hWC wb m γ x))

@[expose, instance_reducible] noncomputable def fiberAction :
    MulAction (Subgroup.normalizer (S : Set G)) wb.index where
  smul := fiberLabel hSC hWC wb
  one_smul := fiberLabel_one hSC hWC wb
  mul_smul := fiberLabel_mul hSC hWC wb


end Action

end KleinFourFiber

open KleinFourFiber


end CFSG.Semidihedral.Principal
