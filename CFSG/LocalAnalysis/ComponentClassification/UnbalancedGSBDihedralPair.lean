module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.NoncommCoprod

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped Pointwise

namespace DihedralPair

section Generators

variable {P : Type*} [Group P] {r b : P}


end Generators

abbrev PairCoord := DihedralGroup 4 × DihedralGroup 4 × Fin 2

@[expose] def pairMul (μ : ℕ) : PairCoord → PairCoord → PairCoord
  | (g, h, 0), (g', h', a) => (g * g', h * h', a)
  | (g, h, 1), (g', h', 0) => (g * h', h * g', 1)
  | (g, h, 1), (g', h', 1) => (g * h' * DihedralGroup.r 2 ^ μ, h * g', 0)

@[expose] def PairEquiv (m m' : PairCoord) : Prop :=
  m'.2.2 = m.2.2 ∧ ((m'.1 = m.1 ∧ m'.2.1 = m.2.1) ∨
    (m'.1 = m.1 * DihedralGroup.r 2 ∧ m'.2.1 = m.2.1 * DihedralGroup.r 2))

instance (m m' : PairCoord) : Decidable (PairEquiv m m') := by
  unfold PairEquiv
  infer_instance

@[expose] def pairU : PairCoord := (DihedralGroup.sr 0, DihedralGroup.sr 0, 0)

@[expose] def pairZ : PairCoord := (DihedralGroup.r 2, 1, 0)


@[expose] def PairInD (μ : ℕ) (m : PairCoord) : Prop :=
  PairEquiv (pairMul μ pairU m) (pairMul μ m pairU)

instance (μ : ℕ) (m : PairCoord) : Decidable (PairInD μ m) := by
  unfold PairInD
  infer_instance


theorem r_two_sq : (DihedralGroup.r 2 : DihedralGroup 4) ^ 2 = 1 := by decide

theorem r_two_inv : (DihedralGroup.r 2 : DihedralGroup 4)⁻¹ = DihedralGroup.r 2 := by decide

theorem r_two_comm (g : DihedralGroup 4) : g * DihedralGroup.r 2 = DihedralGroup.r 2 * g := by
  revert g
  decide

theorem r_two_ne_one : (DihedralGroup.r 2 : DihedralGroup 4) ≠ 1 := by decide

theorem mem_zpowers_eq_one_or_eq {G : Type*} [Group G] {g x : G} (hg : orderOf g = 2)
    (hx : x ∈ zpowers g) : x = 1 ∨ x = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hg]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

variable {H : Type*} [Group H]

structure Model (φ₀ φ₁ : DihedralGroup 4 →* H) (z τ : H) (μ : ℕ) : Prop where
  inj₀ : Function.Injective φ₀
  inj₁ : Function.Injective φ₁
  zeta₀ : φ₀ (DihedralGroup.r 2) = z
  zeta₁ : φ₁ (DihedralGroup.r 2) = z
  central : z ∈ center H
  inter : φ₀.range ⊓ φ₁.range = zpowers z
  comm : ∀ x y, φ₁ y * φ₀ x = φ₀ x * φ₁ y
  sq : τ ^ 2 = z ^ μ
  swap₀ : ∀ x, τ * φ₀ x * τ⁻¹ = φ₁ x
  swap₁ : ∀ x, τ * φ₁ x * τ⁻¹ = φ₀ x
  not_mem : τ ∉ (φ₀.range : Set H) * (φ₁.range : Set H)
  gen : closure ((φ₀.range : Set H) ∪ φ₁.range ∪ {τ}) = ⊤

@[expose] def elem (φ₀ φ₁ : DihedralGroup 4 →* H) (τ : H) (m : PairCoord) : H :=
  φ₀ m.1 * φ₁ m.2.1 * τ ^ (m.2.2 : ℕ)

namespace Model

variable {φ₀ φ₁ : DihedralGroup 4 →* H} {z τ : H} {μ : ℕ}

theorem swap₀' (hM : Model φ₀ φ₁ z τ μ) (x : DihedralGroup 4) : τ * φ₀ x = φ₁ x * τ := by
  rw [← hM.swap₀ x]
  group

theorem swap₁' (hM : Model φ₀ φ₁ z τ μ) (x : DihedralGroup 4) : τ * φ₁ x = φ₀ x * τ := by
  rw [← hM.swap₁ x]
  group

theorem z_sq (hM : Model φ₀ φ₁ z τ μ) : z ^ 2 = 1 := by
  rw [← hM.zeta₀, ← map_pow, r_two_sq, map_one]

theorem orderOf_z (hM : Model φ₀ φ₁ z τ μ) : orderOf z = 2 := by
  apply orderOf_eq_prime hM.z_sq
  rw [← hM.zeta₀, ← map_one φ₀]
  exact fun h => r_two_ne_one (hM.inj₀ h)

theorem elem_mul (hM : Model φ₀ φ₁ z τ μ) (m m' : PairCoord) :
    elem φ₀ φ₁ τ m * elem φ₀ φ₁ τ m' = elem φ₀ φ₁ τ (pairMul μ m m') := by
  obtain ⟨g, h, a⟩ := m
  obtain ⟨g', h', a'⟩ := m'
  have hc := hM.comm
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  have ha' : a' = 0 ∨ a' = 1 := by fin_cases a' <;> simp
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
  · change φ₀ g * φ₁ h * τ ^ 0 * (φ₀ g' * φ₁ h' * τ ^ 0) =
      φ₀ (g * g') * φ₁ (h * h') * τ ^ 0
    rw [pow_zero, mul_one, mul_one, mul_one, map_mul, map_mul]
    calc φ₀ g * φ₁ h * (φ₀ g' * φ₁ h') = φ₀ g * (φ₁ h * φ₀ g') * φ₁ h' := by
          simp only [mul_assoc]
      _ = φ₀ g * (φ₀ g' * φ₁ h) * φ₁ h' := by rw [hc]
      _ = φ₀ g * φ₀ g' * (φ₁ h * φ₁ h') := by simp only [mul_assoc]
  · change φ₀ g * φ₁ h * τ ^ 0 * (φ₀ g' * φ₁ h' * τ ^ 1) =
      φ₀ (g * g') * φ₁ (h * h') * τ ^ 1
    rw [pow_zero, mul_one, map_mul, map_mul]
    calc φ₀ g * φ₁ h * (φ₀ g' * φ₁ h' * τ ^ 1) =
        φ₀ g * (φ₁ h * φ₀ g') * φ₁ h' * τ ^ 1 := by simp only [mul_assoc]
      _ = φ₀ g * (φ₀ g' * φ₁ h) * φ₁ h' * τ ^ 1 := by rw [hc]
      _ = φ₀ g * φ₀ g' * (φ₁ h * φ₁ h') * τ ^ 1 := by simp only [mul_assoc]
  · change φ₀ g * φ₁ h * τ ^ 1 * (φ₀ g' * φ₁ h' * τ ^ 0) =
      φ₀ (g * h') * φ₁ (h * g') * τ ^ 1
    rw [pow_zero, pow_one, mul_one, map_mul, map_mul]
    calc φ₀ g * φ₁ h * τ * (φ₀ g' * φ₁ h') = φ₀ g * φ₁ h * (τ * φ₀ g') * φ₁ h' := by
          simp only [mul_assoc]
      _ = φ₀ g * φ₁ h * (φ₁ g' * τ) * φ₁ h' := by rw [hM.swap₀']
      _ = φ₀ g * φ₁ h * φ₁ g' * (τ * φ₁ h') := by simp only [mul_assoc]
      _ = φ₀ g * φ₁ h * φ₁ g' * (φ₀ h' * τ) := by rw [hM.swap₁']
      _ = φ₀ g * (φ₁ (h * g') * φ₀ h') * τ := by simp only [map_mul, mul_assoc]
      _ = φ₀ g * (φ₀ h' * φ₁ (h * g')) * τ := by rw [hc]
      _ = φ₀ g * φ₀ h' * (φ₁ h * φ₁ g') * τ := by simp only [map_mul, mul_assoc]
  · change φ₀ g * φ₁ h * τ ^ 1 * (φ₀ g' * φ₁ h' * τ ^ 1) =
      φ₀ (g * h' * DihedralGroup.r 2 ^ μ) * φ₁ (h * g') * τ ^ 0
    rw [pow_zero, pow_one, mul_one, map_mul, map_mul, map_pow, hM.zeta₀]
    have hzc : ∀ y : H, y * z ^ μ = z ^ μ * y := fun y =>
      mem_center_iff.mp (pow_mem hM.central μ) y
    calc φ₀ g * φ₁ h * τ * (φ₀ g' * φ₁ h' * τ) =
        φ₀ g * φ₁ h * (τ * φ₀ g') * φ₁ h' * τ := by simp only [mul_assoc]
      _ = φ₀ g * φ₁ h * (φ₁ g' * τ) * φ₁ h' * τ := by rw [hM.swap₀']
      _ = φ₀ g * φ₁ h * φ₁ g' * (τ * φ₁ h') * τ := by simp only [mul_assoc]
      _ = φ₀ g * φ₁ h * φ₁ g' * (φ₀ h' * τ) * τ := by rw [hM.swap₁']
      _ = φ₀ g * (φ₁ (h * g') * φ₀ h') * τ ^ 2 := by simp only [map_mul, mul_assoc, pow_two]
      _ = φ₀ g * (φ₀ h' * φ₁ (h * g')) * z ^ μ := by rw [hc, hM.sq]
      _ = φ₀ g * φ₀ h' * (φ₁ (h * g') * z ^ μ) := by simp only [mul_assoc]
      _ = φ₀ g * φ₀ h' * (z ^ μ * φ₁ (h * g')) := by rw [hzc]
      _ = φ₀ g * φ₀ h' * z ^ μ * φ₁ (h * g') := by simp only [mul_assoc]

theorem inv_mul_pair (hM : Model φ₀ φ₁ z τ μ) (x y x' y' : DihedralGroup 4) :
    (φ₀ x * φ₁ y)⁻¹ * (φ₀ x' * φ₁ y') = φ₀ (x⁻¹ * x') * φ₁ (y⁻¹ * y') := by
  calc (φ₀ x * φ₁ y)⁻¹ * (φ₀ x' * φ₁ y') = φ₁ y⁻¹ * φ₀ (x⁻¹ * x') * φ₁ y' := by
        simp only [mul_inv_rev, map_mul, map_inv, mul_assoc]
    _ = φ₀ (x⁻¹ * x') * φ₁ y⁻¹ * φ₁ y' := by rw [hM.comm]
    _ = φ₀ (x⁻¹ * x') * φ₁ (y⁻¹ * y') := by simp only [map_mul, mul_assoc]

theorem elem_eq_iff (hM : Model φ₀ φ₁ z τ μ) (m m' : PairCoord) :
    elem φ₀ φ₁ τ m = elem φ₀ φ₁ τ m' ↔ PairEquiv m m' := by
  obtain ⟨g, h, a⟩ := m
  obtain ⟨g', h', a'⟩ := m'
  have hmemPP : ∀ x y : DihedralGroup 4,
      φ₀ x * φ₁ y ∈ (φ₀.range : Set H) * (φ₁.range : Set H) :=
    fun x y => Set.mul_mem_mul ⟨x, rfl⟩ ⟨y, rfl⟩
  constructor
  · intro heq
    have ha : a' = a := by
      have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      have ha' : a' = 0 ∨ a' = 1 := by fin_cases a' <;> simp
      rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
      · rfl
      · exfalso
        apply hM.not_mem
        change φ₀ g * φ₁ h * τ ^ 0 = φ₀ g' * φ₁ h' * τ ^ 1 at heq
        rw [pow_zero, mul_one, pow_one] at heq
        have hτ : τ = φ₀ (g'⁻¹ * g) * φ₁ (h'⁻¹ * h) := by
          rw [← hM.inv_mul_pair, heq]
          group
        rw [hτ]
        exact hmemPP _ _
      · exfalso
        apply hM.not_mem
        change φ₀ g * φ₁ h * τ ^ 1 = φ₀ g' * φ₁ h' * τ ^ 0 at heq
        rw [pow_zero, mul_one, pow_one] at heq
        have hτ : τ = φ₀ (g⁻¹ * g') * φ₁ (h⁻¹ * h') := by
          rw [← hM.inv_mul_pair, ← heq]
          group
        rw [hτ]
        exact hmemPP _ _
      · rfl
    subst ha
    refine ⟨rfl, ?_⟩
    have h2 : φ₀ g * φ₁ h = φ₀ g' * φ₁ h' := mul_right_cancel heq
    have hw : φ₀ (g'⁻¹ * g) = φ₁ (h' * h⁻¹) := by
      calc φ₀ (g'⁻¹ * g) = (φ₀ g')⁻¹ * (φ₀ g * φ₁ h) * (φ₁ h)⁻¹ := by
            simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel, mul_one]
        _ = (φ₀ g')⁻¹ * (φ₀ g' * φ₁ h') * (φ₁ h)⁻¹ := by rw [h2]
        _ = φ₁ (h' * h⁻¹) := by simp only [map_mul, map_inv, inv_mul_cancel_left]
    have hwmem : φ₀ (g'⁻¹ * g) ∈ zpowers z := by
      rw [← hM.inter]
      exact mem_inf.mpr ⟨⟨_, rfl⟩, hw ▸ ⟨_, rfl⟩⟩
    rcases mem_zpowers_eq_one_or_eq hM.orderOf_z hwmem with h1 | h1
    · left
      have hg : g'⁻¹ * g = 1 := hM.inj₀ (by rw [h1, map_one])
      have hh : h' * h⁻¹ = 1 := hM.inj₁ (by rw [← hw, h1, map_one])
      exact ⟨inv_mul_eq_one.mp hg, mul_inv_eq_one.mp hh⟩
    · right
      have hg : g'⁻¹ * g = DihedralGroup.r 2 := hM.inj₀ (by rw [h1, hM.zeta₀])
      have hh : h' * h⁻¹ = DihedralGroup.r 2 := hM.inj₁ (by rw [← hw, h1, hM.zeta₁])
      constructor
      · calc g' = g * (g'⁻¹ * g)⁻¹ := by group
          _ = g * DihedralGroup.r 2 := by rw [hg, r_two_inv]
      · calc h' = h' * h⁻¹ * h := by group
          _ = h * DihedralGroup.r 2 := by rw [hh, r_two_comm]
  · rintro ⟨ha, (⟨hg, hh⟩ | ⟨hg, hh⟩)⟩
    · simp only at ha hg hh
      subst ha hg hh
      rfl
    · simp only at ha hg hh
      rw [ha, hg, hh]
      change φ₀ g * φ₁ h * τ ^ (a : ℕ) =
        φ₀ (g * DihedralGroup.r 2) * φ₁ (h * DihedralGroup.r 2) * τ ^ (a : ℕ)
      rw [map_mul, map_mul, hM.zeta₀, hM.zeta₁]
      congr 1
      have hzc : ∀ y : H, y * z = z * y := fun y => mem_center_iff.mp hM.central y
      calc φ₀ g * φ₁ h = φ₀ g * φ₁ h * (z * z) := by rw [← pow_two, hM.z_sq, mul_one]
        _ = φ₀ g * (φ₁ h * z) * z := by simp only [mul_assoc]
        _ = φ₀ g * (z * φ₁ h) * z := by rw [hzc (φ₁ h)]
        _ = φ₀ g * z * (φ₁ h * z) := by simp only [mul_assoc]

theorem elem_surjective (hM : Model φ₀ φ₁ z τ μ) : Function.Surjective (elem φ₀ φ₁ τ) := by
  have hone : elem φ₀ φ₁ τ (1, 1, 0) = 1 := by
    change φ₀ 1 * φ₁ 1 * τ ^ 0 = 1
    rw [map_one, map_one, pow_zero, mul_one, mul_one]
  let K : Subgroup H :=
    { carrier := Set.range (elem φ₀ φ₁ τ)
      mul_mem' := by
        rintro _ _ ⟨m, rfl⟩ ⟨m', rfl⟩
        exact ⟨pairMul μ m m', (hM.elem_mul m m').symm⟩
      one_mem' := ⟨(1, 1, 0), hone⟩
      inv_mem' := by
        rintro _ ⟨⟨g, h, a⟩, rfl⟩
        have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
        rcases ha with rfl | rfl
        · refine ⟨(g⁻¹, h⁻¹, 0), eq_inv_of_mul_eq_one_right ?_⟩
          rw [hM.elem_mul]
          change elem φ₀ φ₁ τ (g * g⁻¹, h * h⁻¹, 0) = 1
          rw [mul_inv_cancel, mul_inv_cancel, hone]
        · refine ⟨(h⁻¹, g⁻¹ * DihedralGroup.r 2 ^ μ, 1), eq_inv_of_mul_eq_one_right ?_⟩
          rw [hM.elem_mul]
          change elem φ₀ φ₁ τ (g * (g⁻¹ * DihedralGroup.r 2 ^ μ) * DihedralGroup.r 2 ^ μ,
            h * h⁻¹, 0) = 1
          have hsq : g * (g⁻¹ * DihedralGroup.r 2 ^ μ) * DihedralGroup.r 2 ^ μ = 1 := by
            rw [mul_inv_cancel_left, ← pow_add, ← two_mul, pow_mul, r_two_sq, one_pow]
          rw [hsq, mul_inv_cancel, hone] }
  have hle : closure ((φ₀.range : Set H) ∪ φ₁.range ∪ {τ}) ≤ K := by
    rw [closure_le]
    rintro x ((⟨y, rfl⟩ | ⟨y, rfl⟩) | hx)
    · refine ⟨(y, 1, 0), ?_⟩
      change φ₀ y * φ₁ 1 * τ ^ 0 = φ₀ y
      rw [map_one, pow_zero, mul_one, mul_one]
    · refine ⟨(1, y, 0), ?_⟩
      change φ₀ 1 * φ₁ y * τ ^ 0 = φ₁ y
      rw [map_one, pow_zero, mul_one, one_mul]
    · refine ⟨(1, 1, 1), ?_⟩
      change φ₀ 1 * φ₁ 1 * τ ^ 1 = x
      rw [map_one, map_one, pow_one, one_mul, one_mul, Set.mem_singleton_iff.mp hx]
  rw [hM.gen] at hle
  intro x
  exact hle (mem_top x)

theorem card_fiber (hM : Model φ₀ φ₁ z τ μ) (x : H) :
    Nat.card {m : PairCoord // elem φ₀ φ₁ τ m = x} = 2 := by
  obtain ⟨m₀, rfl⟩ := hM.elem_surjective x
  obtain ⟨g₀, h₀, a₀⟩ := m₀
  have hset : {m : PairCoord | elem φ₀ φ₁ τ m = elem φ₀ φ₁ τ (g₀, h₀, a₀)} =
      {(g₀, h₀, a₀), (g₀ * DihedralGroup.r 2, h₀ * DihedralGroup.r 2, a₀)} := by
    ext ⟨g, h, a⟩
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [eq_comm, hM.elem_eq_iff]
    simp only [PairEquiv, Prod.mk.injEq]
    tauto
  have hne : ((g₀, h₀, a₀) : PairCoord) ≠
      (g₀ * DihedralGroup.r 2, h₀ * DihedralGroup.r 2, a₀) := by
    intro h
    apply r_two_ne_one
    have h1 : g₀ = g₀ * DihedralGroup.r 2 := congrArg Prod.fst h
    calc (DihedralGroup.r 2 : DihedralGroup 4) = g₀⁻¹ * (g₀ * DihedralGroup.r 2) := by group
      _ = 1 := by rw [← h1, inv_mul_cancel]
  change Nat.card ↥{m : PairCoord | elem φ₀ φ₁ τ m = elem φ₀ φ₁ τ (g₀, h₀, a₀)} = 2
  rw [hset, Nat.card_coe_set_eq, Set.ncard_pair hne]


end Model

theorem klein_closure {G : Type*} [Group G] {z u : G} (hz : orderOf z = 2)
    (hu : orderOf u = 2) (hzu : z * u = u * z) (hne : u ∉ zpowers z) :
    IsElementaryAbelian 2 (closure {z, u}) ∧ Nat.card (closure {z, u}) = 4 := by
  have hcomm : ∀ (x : zpowers z) (y : zpowers u),
      Commute ((zpowers z).subtype x) ((zpowers u).subtype y) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow hzu i j)
  let φ := (zpowers z).subtype.noncommCoprod (zpowers u).subtype hcomm
  have hrange : φ.range = closure {z, u} := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype, Set.insert_eq,
      closure_union, zpowers_eq_closure, zpowers_eq_closure]
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨subtype_injective _, subtype_injective _, ?_⟩
    rw [range_subtype, range_subtype, disjoint_iff]
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨hxz, hxu⟩ := mem_inf.mp hx
    rcases mem_zpowers_eq_one_or_eq hu hxu with h | h
    · rw [h]
      exact one_mem _
    · exact absurd (h ▸ hxz) hne
  have hcard : Nat.card (closure {z, u}) = 4 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
      Nat.card_zpowers, Nat.card_zpowers, hz, hu]
  have hle : closure {z, u} ≤ centralizer ((closure {z, u} : Subgroup G) : Set G) := by
    rw [centralizer_closure, closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hzu.symm
    · exact hzu
    · rfl
  have hcommK : ∀ x ∈ closure {z, u}, ∀ y ∈ closure {z, u}, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp (hle hx) y hy).symm
  have hsq : ∀ x ∈ closure {z, u}, x ^ 2 = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · rw [← hz, pow_orderOf_eq_one]
      · rw [← hu, pow_orderOf_eq_one]
    | one => exact one_pow 2
    | mul a b ha hb iha ihb =>
      rw [(Commute.mul_pow (hcommK a ha b hb) 2), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hcommInst : IsMulCommutative (closure {z, u}) :=
    isMulCommutative_iff.mpr fun a b => Subtype.ext (hcommK _ a.2 _ b.2)
  refine ⟨@IsElementaryAbelian.mk 2 _ _ hcommInst ?_, hcard⟩
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro g
  exact Subtype.ext (by simpa using hsq g g.2)

end DihedralPair

open DihedralPair


end CFSG.ComponentClassification.UnbalancedGS
