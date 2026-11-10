module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique

namespace L246C127

namespace C127Block


theorem perm_two_subgroup_dichotomy {n : ℕ} (hodd : Odd n) (h5 : 5 ≤ n)
    (S : Subgroup (Equiv.Perm (Fin n))) (hS : IsPGroup 2 S) :
    (∃ O : Finset (Fin n), (∀ s ∈ S, ∀ x ∈ O, s x ∈ O) ∧ 2 ≤ O.card ∧ O.card + 2 ≤ n) ∨
      ∃ j : ℕ, n = 2 ^ j + 1 := by
  classical
  have hcong : Nat.card (Fin n) ≡ Nat.card (MulAction.fixedPoints S (Fin n)) [MOD 2] :=
    hS.card_modEq_card_fixedPoints (Fin n)
  have hn : Nat.card (Fin n) = n := by simp
  rw [hn] at hcong
  have hc_odd : Nat.card (MulAction.fixedPoints S (Fin n)) % 2 = 1 := by
    unfold Nat.ModEq at hcong
    rw [← hcong]
    exact Nat.odd_iff.1 hodd
  have hfixS : ∀ y : Fin n, (∀ g : S, g • y = y) → ∀ s ∈ S, s y = y :=
    fun y hy s hs => hy ⟨s, hs⟩
  rcases (show Nat.card (MulAction.fixedPoints S (Fin n)) = 1 ∨
      2 ≤ Nat.card (MulAction.fixedPoints S (Fin n)) by omega) with hc1 | hc2
  ·
    obtain ⟨ω, hωfix, huniq⟩ : ∃ ω : Fin n, (∀ g : S, g • ω = ω) ∧
        ∀ y : Fin n, (∀ g : S, g • y = y) → y = ω := by
      obtain ⟨ω0, hω0⟩ := Nat.card_eq_one_iff_exists.1 hc1
      exact ⟨ω0.1, MulAction.mem_fixedPoints.1 ω0.2, fun y hy =>
        congrArg Subtype.val (hω0 ⟨y, MulAction.mem_fixedPoints.2 hy⟩)⟩
    obtain ⟨x, hxω⟩ : ∃ x : Fin n, x ≠ ω :=
      Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) ω
    obtain ⟨O, hO⟩ : ∃ O : Finset (Fin n), ∀ y, y ∈ O ↔ ∃ g : S, g • x = y :=
      ⟨Finset.univ.filter (fun y => ∃ g : S, g • x = y), fun y => by simp⟩
    have hinv : ∀ s ∈ S, ∀ y ∈ O, s y ∈ O := by
      intro s hs y hy
      obtain ⟨g, rfl⟩ := (hO y).1 hy
      refine (hO _).2 ⟨⟨s, hs⟩ * g, ?_⟩
      exact mul_smul _ _ _
    obtain ⟨m, hm⟩ := hS.card_orbit x
    have hOset : (O : Set (Fin n)) = MulAction.orbit S x := by
      ext y
      rw [Finset.mem_coe, hO, MulAction.mem_orbit_iff]
    have hOcard : O.card = 2 ^ m := by
      rw [← hm, ← hOset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hxO : x ∈ O := (hO x).2 ⟨1, by simp⟩
    have hm0 : m ≠ 0 := by
      intro hm0
      rw [hm0, pow_zero] at hOcard
      have hxfix : ∀ g : S, g • x = x := fun g =>
        Finset.card_le_one.1 (le_of_eq hOcard) (g • x) ((hO _).2 ⟨g, rfl⟩) x hxO
      exact hxω (huniq x hxfix)
    have hyω : ∀ y ∈ O, y ≠ ω := by
      intro y hy hyeq
      obtain ⟨g, hg⟩ := (hO y).1 hy
      apply hxω
      calc x = g⁻¹ • g • x := (inv_smul_smul g x).symm
        _ = g⁻¹ • ω := by rw [hg, hyeq]
        _ = ω := hωfix g⁻¹
    have hsub : O ⊆ Finset.univ.erase ω := fun y hy =>
      Finset.mem_erase.2 ⟨hyω y hy, Finset.mem_univ y⟩
    have hle : O.card + 1 ≤ n := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ ω), Finset.card_univ, Fintype.card_fin] at h1
      omega
    have h2 : 2 ≤ O.card := by
      rw [hOcard]
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hm0)
    by_cases hfin : O.card + 2 ≤ n
    · exact Or.inl ⟨O, hinv, h2, hfin⟩
    · exact Or.inr ⟨m, by omega⟩
  ·
    have hnt : Nontrivial (MulAction.fixedPoints S (Fin n)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (MulAction.fixedPoints S (Fin n))
    have hne : (a : Fin n) ≠ (b : Fin n) := fun h => hab (Subtype.ext h)
    have hfa : ∀ s ∈ S, s (a : Fin n) = a := fun s hs =>
      hfixS _ (MulAction.mem_fixedPoints.1 a.2) s hs
    have hfb : ∀ s ∈ S, s (b : Fin n) = b := fun s hs =>
      hfixS _ (MulAction.mem_fixedPoints.1 b.2) s hs
    have hcard : ({(a : Fin n), (b : Fin n)} : Finset (Fin n)).card = 2 :=
      Finset.card_pair hne
    refine Or.inl ⟨{(a : Fin n), (b : Fin n)}, ?_, ?_, ?_⟩
    · intro s hs x hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · rw [hfa s hs]
        exact Finset.mem_insert_self _ _
      · rw [Finset.mem_singleton.1 hx', hfb s hs]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · omega
    · omega

@[expose] def young {n : ℕ} (O : Finset (Fin n)) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ x, σ x ∈ O ↔ x ∈ O}
  one_mem' := by
    intro x
    first
    | exact Iff.rfl
    | simp
  mul_mem' := by
    intro σ τ hσ hτ x
    rw [Equiv.Perm.mul_apply]
    exact (hσ (τ x)).trans (hτ x)
  inv_mem' := by
    intro σ hσ x
    have h := hσ (σ⁻¹ x)
    have hx : σ (σ⁻¹ x) = x := by
      first
      | (rw [Equiv.Perm.inv_def]; exact Equiv.apply_symm_apply σ x)
      | simp
    rw [hx] at h
    exact h.symm

theorem mem_young_iff {n : ℕ} {O : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} :
    σ ∈ young O ↔ ∀ x, σ x ∈ O ↔ x ∈ O := Iff.rfl

theorem mem_young_of_forall_mem {n : ℕ} (O : Finset (Fin n)) {s : Equiv.Perm (Fin n)}
    (hs : ∀ x ∈ O, s x ∈ O) : s ∈ young O := by
  rw [mem_young_iff]
  intro x
  refine ⟨fun hx => ?_, hs x⟩
  have hsub : O.image s ⊆ O := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact hs z hz
  have hcard : (O.image s).card = O.card := Finset.card_image_of_injective O s.injective
  have heq : O.image s = O := Finset.eq_of_subset_of_card_le hsub hcard.symm.le
  have hx' : s x ∈ O.image s := by
    rw [heq]
    exact hx
  obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx'
  have hzx' : z = x := s.injective hzx
  rw [← hzx']
  exact hz

theorem bt_swap_mem_young {n : ℕ} {O : Finset (Fin n)} {a b : Fin n}
    (h : a ∈ O ↔ b ∈ O) : Equiv.swap a b ∈ young O := by
  rw [mem_young_iff]
  intro z
  rw [Equiv.swap_apply_def]
  by_cases h1 : z = a
  · rw [if_pos h1, h1]
    exact h.symm
  · by_cases h2 : z = b
    · rw [if_neg h1, if_pos h2, h2]
      exact h
    · rw [if_neg h1, if_neg h2]

theorem bt_exists_ne_mem {n : ℕ} (O : Finset (Fin n)) (h2 : 2 ≤ O.card) (a : Fin n) :
    ∃ x ∈ O, x ≠ a := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < O.card)
  by_cases h : x = a
  · exact ⟨y, hy, fun h' => hxy (h.trans h'.symm)⟩
  · exact ⟨x, hx, h⟩

theorem bt_exists_notMem_ne {n : ℕ} (O : Finset (Fin n)) (hO : O.card + 2 ≤ n) (a : Fin n) :
    ∃ y, y ∉ O ∧ y ≠ a := by
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ insert a O := by
    intro z _
    by_cases hz : z ∈ O
    · exact Finset.mem_insert_of_mem hz
    · exact Finset.mem_insert.mpr (Or.inl (hc z hz))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Finset.card_insert_le a O
  omega

theorem bt_exists_ne_two {n : ℕ} (a b : Fin n) (h : 3 ≤ n) :
    ∃ q : Fin n, q ≠ a ∧ q ≠ b := by
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ insert a {b} := by
    intro z _
    by_cases hz : z = a
    · exact Finset.mem_insert.mpr (Or.inl hz)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hc z hz)))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Finset.card_insert_le a ({b} : Finset (Fin n))
  rw [Finset.card_singleton] at h2
  omega

theorem exists_even_not_mem_young {n : ℕ} (O : Finset (Fin n)) (h2 : 2 ≤ O.card)
    (hO : O.card + 2 ≤ n) : ∃ σ ∈ alternatingGroup (Fin n), σ ∉ young O := by
  obtain ⟨a, ha⟩ : O.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp, -⟩ := bt_exists_notMem_ne O hO a
  obtain ⟨q, hqa, hqp⟩ := bt_exists_ne_two a p (by omega)
  have hap : a ≠ p := fun h => hp (by rw [← h]; exact ha)
  have hpq : p ≠ q := fun h => hqp h.symm
  have haq : a ≠ q := fun h => hqa h.symm
  refine ⟨Equiv.swap a p * Equiv.swap p q, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hap,
      Equiv.Perm.sign_swap hpq]
    all_goals first | rfl | decide | norm_num | simp
  · intro hmem
    have h1 := (mem_young_iff.mp hmem) a
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hap haq,
      Equiv.swap_apply_left] at h1
    exact hp (h1.mpr ha)


end C127Block

end L246C127

end CFSG.QuasithinUnique
