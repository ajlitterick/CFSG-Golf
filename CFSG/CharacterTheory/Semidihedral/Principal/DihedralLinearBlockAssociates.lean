module

public import CFSG.CharacterTheory.Semidihedral.Principal.ControlledDefectCorrespondence
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralizerBrauerDefect
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralRotationInvolutionStructure
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerLinearFamily

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.GorensteinWalter

namespace DihedralAssociates

variable {G : Type*} [Group G]

theorem dihedral_facts [Finite G] {n : ℕ} (hn : 2 ≤ n) (S : Subgroup G)
    (hScard : Nat.card S = 2 * 2 ^ (n - 1)) (r s : G) (hr : orderOf r = 2 ^ (n - 1))
    (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹) (hgen : Subgroup.closure ({r, s} : Set G) = S) :
    r ∈ S ∧ s ∈ S ∧ Subgroup.zpowers r ≤ S ∧
    (∀ y ∈ S, y * r ^ 2 ^ (n - 2) = r ^ 2 ^ (n - 2) * y) ∧ orderOf (r ^ 2 ^ (n - 2)) = 2 ∧
    (∀ a ∈ Subgroup.zpowers r, a * a = 1 → a = 1 ∨ a = r ^ 2 ^ (n - 2)) ∧
    (∀ x ∈ S, x ∉ Subgroup.zpowers r → x * x = 1) ∧
    (∀ x ∈ S, x ∉ Subgroup.zpowers r → ∃ j : ℕ, x = s * r ^ j) ∧
    (∀ x ∈ S, x ∉ Subgroup.zpowers r →
      Nat.card (Subgroup.closure ({r ^ 2 ^ (n - 2), x} : Set G)) = 4) := by
  have hrS : r ∈ S := hgen ▸ Subgroup.subset_closure (Set.mem_insert r {s})
  have hsS : s ∈ S := hgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem r rfl)
  have hM2 : 2 ≤ 2 ^ (n - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let r' : S := ⟨r, hrS⟩
  let s' : S := ⟨s, hsS⟩
  have hr' : orderOf r' = 2 ^ (n - 1) := by rw [Subgroup.orderOf_mk]; exact hr
  have hs' : orderOf s' = 2 := by rw [Subgroup.orderOf_mk]; exact hs
  have hrel' : s' * r' * s' = r'⁻¹ := Subtype.ext hrel
  have hgen' : Subgroup.closure ({r', s'} : Set S) = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective S)
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hgen
  have hrM' : r' ^ 2 ^ (n - 1) = 1 := hr' ▸ pow_orderOf_eq_one r'
  have hss' : s' * s' = 1 := by rw [← pow_two, ← hs', pow_orderOf_eq_one]
  have hdih : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* S) := by
    obtain ⟨e, -, -⟩ := exists_dihedral_mulEquiv hM2 hScard hgen' hrM' hss' hrel'
    exact ⟨e⟩
  obtain ⟨-, hall⟩ := dihedral_rotation_involution_structure hn hdih
  obtain ⟨-, -, hnf, ⟨-, hzord, hzuniq⟩, hinvol, hzcenter, -, -, hcentx, -⟩ :=
    hall r' s' hr' hs' hrel' hgen'
  have hA : ∀ (y : G) (hy : y ∈ S), (⟨y, hy⟩ : S) ∈ Subgroup.zpowers r' ↔
      y ∈ Subgroup.zpowers r := by
    intro y hy
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [r'] using congrArg Subtype.val hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa [r'] using hk)⟩
  have hAS : Subgroup.zpowers r ≤ S := (Subgroup.zpowers_le).mpr hrS
  refine ⟨hrS, hsS, hAS, fun y hy => ?_, ?_, fun a ha haa => ?_, fun x hx hxA => ?_,
    fun x hx hxA => ?_, fun x hx hxA => ?_⟩
  · have hc := Subgroup.mem_center_iff.mp hzcenter ⟨y, hy⟩
    exact congrArg Subtype.val hc
  · have h := hzord
    rw [← Subgroup.orderOf_coe] at h
    exact h
  · by_cases ha1 : a = 1
    · exact Or.inl ha1
    · right
      have haS : a ∈ S := hAS ha
      have hord : orderOf (⟨a, haS⟩ : S) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (by rw [pow_two, haa]) ha1
      have heq := hzuniq ⟨a, haS⟩ ((hA a haS).mpr ha) hord
      exact congrArg Subtype.val heq
  · have hord := hinvol ⟨x, hx⟩ (fun h => hxA ((hA x hx).mp h))
    rw [Subgroup.orderOf_mk] at hord
    rw [← pow_two, ← hord, pow_orderOf_eq_one]
  · obtain ⟨c, hc, -⟩ := hnf ⟨x, hx⟩
    have h2 := c.1.isLt
    rcases (by omega : (c.1 : ℕ) = 0 ∨ (c.1 : ℕ) = 1) with h0 | h1
    · exfalso
      rw [h0, pow_zero, one_mul] at hc
      apply hxA
      rw [← hA x hx, hc]
      exact Subgroup.npow_mem_zpowers r' _
    · rw [h1, pow_one] at hc
      exact ⟨c.2, by simpa [r', s'] using congrArg Subtype.val hc⟩
  · obtain ⟨-, hK4⟩ := hcentx ⟨x, hx⟩ (fun h => hxA ((hA x hx).mp h))
    have hmap : (Subgroup.closure ({r' ^ 2 ^ (n - 2), ⟨x, hx⟩} : Set S)).map S.subtype =
        Subgroup.closure ({r ^ 2 ^ (n - 2), x} : Set G) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective S)]
    exact hK4.card_four

theorem reflection_inverts (S A : Subgroup G) (hAS : A ≤ S)
    (hinv : ∀ x ∈ S, x ∉ A → x * x = 1) {x : G} (hx : x ∈ S) (hxA : x ∉ A) {a : G}
    (ha : a ∈ A) : x * a * x⁻¹ = a⁻¹ := by
  have hxa : x * a ∉ A := fun h => hxA (by simpa using A.mul_mem h (A.inv_mem ha))
  have h1 : (x * a) * (x * a) = 1 := hinv _ (S.mul_mem hx (hAS ha)) hxa
  have hx2 : x * x = 1 := hinv x hx hxA
  rw [inv_eq_of_mul_eq_one_right hx2]
  calc x * a * x = x * a * x * (a * a⁻¹) := by rw [mul_inv_cancel, mul_one]
    _ = ((x * a) * (x * a)) * a⁻¹ := by group
    _ = a⁻¹ := by rw [h1, one_mul]

theorem mem_centralizer_zpowers_of_commute {t g : G} (h : g * t = t * g) :
    g ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc : Commute t g := (show Commute g t from h).symm
  exact (hc.zpow_left k).eq

theorem dichotomy (S A : Subgroup G) {t : G} (hAS : A ≤ S) (htA : t ∈ A) (ht1 : t ≠ 1)
    (htt : t * t = 1) (htc : ∀ y ∈ S, y * t = t * y)
    (huniq : ∀ a ∈ A, a * a = 1 → a = 1 ∨ a = t) (hinv : ∀ x ∈ S, x ∉ A → x * x = 1)
    (hidx : ∀ x ∈ S, ∀ y ∈ S, x ∉ A → y ∉ A → x⁻¹ * y ∈ A) (D : Subgroup G) (htD : t ∈ D)
    (hDS : D ≤ S) :
    (∃ x ∈ D, x ∉ A ∧ D = Subgroup.closure ({t, x} : Set G)) ∨
      Subgroup.normalizer (D : Set G) ≤
        Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  by_cases hcase : ∃ x ∈ D, x ∉ A ∧ ∀ a ∈ D, a ∈ A → a = 1 ∨ a = t
  · left
    obtain ⟨x, hxD, hxA, hsmall⟩ := hcase
    refine ⟨x, hxD, hxA, le_antisymm ?_ ((Subgroup.closure_le D).mpr
      (Set.insert_subset_iff.mpr ⟨htD, Set.singleton_subset_iff.mpr hxD⟩))⟩
    intro y hy
    have htmem : t ∈ Subgroup.closure ({t, x} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert t {x})
    have hxmem : x ∈ Subgroup.closure ({t, x} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem t rfl)
    by_cases hyA : y ∈ A
    · rcases hsmall y hy hyA with rfl | rfl
      · exact Subgroup.one_mem _
      · exact htmem
    · have hxy := hidx x (hDS hxD) y (hDS hy) hxA hyA
      have hy' : y = x * (x⁻¹ * y) := by group
      rcases hsmall (x⁻¹ * y) (D.mul_mem (D.inv_mem hxD) hy) hxy with h | h
      · rw [hy', h, mul_one]
        exact hxmem
      · rw [hy', h]
        exact Subgroup.mul_mem _ hxmem htmem
  · right
    intro g hg
    apply mem_centralizer_zpowers_of_commute
    have hnorm := Subgroup.mem_normalizer_iff.mp hg
    have ht'D : g * t * g⁻¹ ∈ D := (hnorm t).mp htD
    have ht't' : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [htt]; group
    have ht'c : ∀ y ∈ D, y * (g * t * g⁻¹) = (g * t * g⁻¹) * y := by
      intro y hy
      have hy' : g⁻¹ * y * g ∈ D := by
        apply (hnorm (g⁻¹ * y * g)).mpr
        have hval : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [hval]
        exact hy
      have hcomm := htc _ (hDS hy')
      calc y * (g * t * g⁻¹) = g * ((g⁻¹ * y * g) * t) * g⁻¹ := by group
        _ = g * (t * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * t * g⁻¹) * y := by group
    have ht'eq : g * t * g⁻¹ = t := by
      by_cases ht'A : g * t * g⁻¹ ∈ A
      · rcases huniq _ ht'A ht't' with h | h
        · exact absurd (conj_eq_one_iff.mp h) ht1
        · exact h
      · exfalso
        apply hcase
        refine ⟨g * t * g⁻¹, ht'D, ht'A, fun a haD haA => huniq a haA ?_⟩
        have hinvert := reflection_inverts S A hAS hinv (hDS ht'D) ht'A haA
        have hc := ht'c a haD
        have hfix : (g * t * g⁻¹) * a * (g * t * g⁻¹)⁻¹ = a := by
          rw [← hc]
          group
        rw [hfix] at hinvert
        calc a * a = a * a⁻¹ := by rw [← hinvert]
          _ = 1 := mul_inv_cancel a
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [ht'eq]


end DihedralAssociates

open DihedralAssociates


end CFSG.Semidihedral.Principal
