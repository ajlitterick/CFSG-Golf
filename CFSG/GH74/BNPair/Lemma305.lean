module

public import CFSG.GH74.BNPair.Positions

public section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

section LProd

variable {X : Type*} [Group X]

@[expose] def lprod {α : Type*} (A : α → Subgroup X) (l : List α) : Set X :=
  (l.map fun k => (A k : Set X)).prod

theorem chainProd_eq_lprod (A : ℤ → Subgroup X) (l : List ℤ) : chainProd A l = lprod A l := rfl

theorem lprod_nil {α : Type*} (A : α → Subgroup X) : lprod A [] = 1 := by simp [lprod]

theorem lprod_cons {α : Type*} (A : α → Subgroup X) (a : α) (l : List α) :
    lprod A (a :: l) = (A a : Set X) * lprod A l := by simp [lprod]

theorem lprod_map {α β : Type*} (A : β → Subgroup X) (f : α → β) (l : List α) :
    lprod A (l.map f) = lprod (fun a => A (f a)) l := by
  simp [lprod, List.map_map, Function.comp_def]

theorem lprod_map_conj {α β : Type*} (A : α → Subgroup X) (B : β → Subgroup X) (f : α → β) (m : X) :
    ∀ l : List α, (∀ a ∈ l, ∀ x ∈ A a, m * x * m⁻¹ ∈ B (f a)) →
      (∀ a ∈ l, ∀ y ∈ B (f a), m⁻¹ * y * m ∈ A a) →
      lprod B (l.map f) = (fun x => m * x * m⁻¹) '' lprod A l
  | [], _, _ => by
    ext z
    simp only [List.map_nil, lprod_nil, Set.mem_one, Set.mem_image]
    constructor
    · rintro rfl
      exact ⟨1, rfl, by simp⟩
    · rintro ⟨x, rfl, rfl⟩
      simp
  | a :: l, hf, hb => by
    have ih := lprod_map_conj A B f m l (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha'))
      (fun a' ha' => hb a' (List.mem_cons_of_mem _ ha'))
    rw [List.map_cons, lprod_cons, lprod_cons, ih]
    ext z
    constructor
    · intro hz
      obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_mul.1 hz
      obtain ⟨t₀, ht₀, rfl⟩ := ht
      refine ⟨(m⁻¹ * s * m) * t₀, Set.mem_mul.2 ⟨_, hb a List.mem_cons_self s hs, t₀, ht₀, rfl⟩, ?_⟩
      simp only
      group
    · rintro ⟨_, hz, rfl⟩
      obtain ⟨x, hx, t₀, ht₀, rfl⟩ := Set.mem_mul.1 hz
      refine Set.mem_mul.2 ⟨m * x * m⁻¹, hf a List.mem_cons_self x hx, m * t₀ * m⁻¹,
        ⟨t₀, ht₀, rfl⟩, ?_⟩
      group

end LProd

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

@[expose] def pprod (L : List ℤ) : Set X :=
  lprod (fun q => D.root (Rt n q)) L

@[expose] def GoodPos (L : List ℤ) : Prop :=
  (∃ V : Subgroup X, (V : Set X) = D.pprod L) ∧ D.pprod L = D.pprod L.reverse

variable {D}

theorem pprod_eq_chainProd (L : List ℤ) : D.pprod L = chainProd D.root (L.map (Rt n)) := by
  unfold pprod
  rw [chainProd_eq_lprod, lprod_map]

theorem GoodPos.reverse {L : List ℤ} (h : D.GoodPos L) : D.GoodPos L.reverse := by
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨V, hV⟩, h2⟩ := h
    exact ⟨V, hV.trans h2⟩
  · rw [List.reverse_reverse]
    exact h.2.symm

theorem GoodPos.map {L : List ℤ} (hL : D.GoodPos L) {m : X} {ρ : ℤ → ℤ} (hρ : ∀ q, ρ (ρ q) = q)
    (hm : D.ActsPos m ρ) (hm' : D.ActsPos m⁻¹ ρ) : D.GoodPos (L.map ρ) := by
  have key : ∀ L' : List ℤ, D.pprod (L'.map ρ) = (fun x => m * x * m⁻¹) '' D.pprod L' := by
    intro L'
    exact lprod_map_conj (fun q => D.root (Rt n q)) (fun q => D.root (Rt n q)) ρ m L'
      (fun q _ x hx => hm q x hx) (fun q _ y hy => by
        have := hm' (ρ q) y hy
        rwa [hρ q, inv_inv] at this)
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨V, hV⟩, -⟩ := hL
    refine ⟨V.map (MulAut.conj m).toMonoidHom, ?_⟩
    rw [key, ← hV]
    ext x
    simp [Subgroup.coe_map, MulAut.conj_apply]
  · rw [← List.map_reverse, key, key, ← hL.2]

end RankTwoSystem

@[expose] def plist (p : ℤ) (k : ℕ) : List ℤ :=
  (List.range (k + 1)).map fun t : ℕ => p + t


theorem plist_map_reflect (c p : ℤ) (k : ℕ) :
    (plist p k).map (fun q => c - q) = (plist (c - p - k) k).reverse := by
  apply List.ext_getElem
  · simp [plist]
  · intro t h1 h2
    simp only [plist, List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map,
      List.length_range]
    have : t < k + 1 := by simpa [plist] using h1
    push_cast [Nat.sub_sub, Nat.cast_sub (show k - t ≤ k by omega)]
    rw [Nat.cast_sub (by omega)]
    ring

theorem plist_map_Rt_zero {n k : ℕ} (hk : k < n) : (plist 0 k).map (Rt n) = intList 1 (k + 1) := by
  apply List.ext_getElem
  · simp [plist, intList]
  · intro t h1 h2
    have ht : t < k + 1 := by simpa [plist] using h1
    simp only [plist, intList, List.getElem_map, List.getElem_range]
    rw [Rt_of_lt (by omega) (by omega)]
    ring

theorem plist_map_Rt_one {n k : ℕ} (hk : k + 1 < n) :
    (plist 1 k).map (Rt n) = intList 2 (k + 2) := by
  apply List.ext_getElem
  · simp [plist, intList]
    omega
  · intro t h1 h2
    have ht : t < k + 1 := by simpa [plist] using h1
    simp only [plist, intList, List.getElem_map, List.getElem_range]
    rw [Rt_of_lt (by omega) (by omega)]
    ring

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} {D : RankTwoSystem X n}

theorem good_plist {k : ℕ} (hk : k + 1 ≤ n) : ∀ p : ℤ, D.GoodPos (plist p k) := by
  have hn := D.three_le
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective D.w₁
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective D.w₂
  have refl₁ : ∀ p, D.GoodPos (plist p k) → D.GoodPos (plist ((n : ℤ) - p - k) k) := by
    intro p hp
    have h1 := hp.map (m := (m₁ : X)) (ρ := fun q => (n : ℤ) - q) (fun q => by ring)
      (D.actsPos_lift₁ m₁ hm₁) (by
        have := D.actsPos_lift₁ (m₁⁻¹) (lift₁_inv m₁ hm₁)
        rwa [Subgroup.coe_inv] at this)
    rw [plist_map_reflect] at h1
    simpa using h1.reverse
  have refl₂ : ∀ p, D.GoodPos (plist p k) → D.GoodPos (plist ((n : ℤ) - 2 - p - k) k) := by
    intro p hp
    have h1 := hp.map (m := (m₂ : X)) (ρ := fun q => (n : ℤ) - 2 - q) (fun q => by ring)
      (D.actsPos_lift₂ m₂ hm₂) (by
        have := D.actsPos_lift₂ (m₂⁻¹) (lift₂_inv m₂ hm₂)
        rwa [Subgroup.coe_inv] at this)
    rw [plist_map_reflect] at h1
    simpa using h1.reverse
  have step_up : ∀ p, D.GoodPos (plist p k) → D.GoodPos (plist (p + 2) k) := by
    intro p hp
    have := refl₁ _ (refl₂ _ hp)
    rwa [show (n : ℤ) - ((n : ℤ) - 2 - p - k) - k = p + 2 by ring] at this
  have step_down : ∀ p, D.GoodPos (plist p k) → D.GoodPos (plist (p - 2) k) := by
    intro p hp
    have := refl₂ _ (refl₁ _ hp)
    rwa [show (n : ℤ) - 2 - ((n : ℤ) - p - k) - k = p - 2 by ring] at this
  have base0 : D.GoodPos (plist 0 k) := by
    obtain ⟨V, hVc, -, -, -⟩ := D.roots.subgroup 1 ((k : ℤ) + 1) (by omega) (by omega) (by omega)
    have e := plist_map_Rt_zero (n := n) (k := k) (by omega)
    refine ⟨⟨V, ?_⟩, ?_⟩
    · rw [pprod_eq_chainProd, e]
      exact hVc
    · rw [pprod_eq_chainProd, pprod_eq_chainProd, List.map_reverse, e]
      exact D.roots.reverse_eq 1 ((k : ℤ) + 1) (by omega) (by omega) (by omega)
  have base1 : D.GoodPos (plist 1 k) := by
    by_cases hk2 : k + 2 ≤ n
    · obtain ⟨V, hVc, -, -, -⟩ := D.roots.subgroup 2 ((k : ℤ) + 2) (by omega) (by omega) (by omega)
      have e := plist_map_Rt_one (n := n) (k := k) (by omega)
      refine ⟨⟨V, ?_⟩, ?_⟩
      · rw [pprod_eq_chainProd, e]
        exact hVc
      · rw [pprod_eq_chainProd, pprod_eq_chainProd, List.map_reverse, e]
        exact D.roots.reverse_eq 2 ((k : ℤ) + 2) (by omega) (by omega) (by omega)
    · have hkn : k + 1 = n := by omega
      have := refl₁ _ base0
      rwa [show (n : ℤ) - 0 - k = 1 by omega] at this
  intro p
  obtain ⟨a, rfl | rfl⟩ := Int.even_or_odd' p
  · induction a using Int.induction_on with
    | zero => simpa using base0
    | succ a ih =>
      have := step_up _ ih
      rwa [show 2 * (a : ℤ) + 2 = 2 * ((a : ℤ) + 1) by ring] at this
    | pred a ih =>
      have := step_down _ ih
      rwa [show 2 * (-(a : ℤ)) - 2 = 2 * (-(a : ℤ) - 1) by ring] at this
  · induction a using Int.induction_on with
    | zero => simpa using base1
    | succ a ih =>
      have := step_up _ ih
      rwa [show 2 * (a : ℤ) + 1 + 2 = 2 * ((a : ℤ) + 1) + 1 by ring] at this
    | pred a ih =>
      have := step_down _ ih
      rwa [show 2 * (-(a : ℤ)) + 1 - 2 = 2 * (-(a : ℤ) - 1) + 1 by ring] at this

end RankTwoSystem

section Arcs


end Arcs

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem chainProd_good_plist {k : ℕ} (hk : k + 1 ≤ n) (p : ℤ) :
    (∃ V : Subgroup X, (V : Set X) = chainProd D.root ((plist p k).map (Rt n))) ∧
      chainProd D.root ((plist p k).map (Rt n)) =
        chainProd D.root ((plist p k).map (Rt n)).reverse := by
  obtain ⟨hV, hrev⟩ := D.good_plist hk p
  rw [pprod_eq_chainProd] at hV hrev
  rw [pprod_eq_chainProd, List.map_reverse] at hrev
  exact ⟨hV, hrev⟩


end RankTwoSystem


end CFSG.GH74.BNPair
