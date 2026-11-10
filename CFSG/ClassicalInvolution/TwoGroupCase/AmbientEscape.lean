module

public import CFSG.ClassicalInvolution.TwoGroupCase.Fusion

public section

namespace CFSG.ClassicalInvolution

open CFSG CFSG.Open
open scoped Pointwise

universe u

variable {G : Type u} [Group G]


theorem exists_mem_normalizer_not_mem_sq_mem [Finite G] {T U : Subgroup G} (hU : IsPGroup 2 U)
    (hTU : T ≤ U) (hne : T ≠ U) :
    ∃ x ∈ U, x ∈ Subgroup.normalizer (T : Set G) ∧ x ∉ T ∧ x * x ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hsU, hsN, hsT⟩ := exists_mem_normalizer_not_mem hU hTU hne
  have hex : ∃ k : ℕ, s ^ (2 ^ k) ∈ T := by
    obtain ⟨k, hk⟩ := hU ⟨s, hsU⟩
    refine ⟨k, ?_⟩
    have h1 : s ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [h1]
    exact T.one_mem
  classical
  have hk₀T : s ^ (2 ^ Nat.find hex) ∈ T := Nat.find_spec hex
  have hk₀pos : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hk₀T
    exact hsT (by simpa using hk₀T)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hk₀pos
  refine ⟨s ^ (2 ^ j), U.pow_mem hsU _, (Subgroup.normalizer (T : Set G)).pow_mem hsN _, ?_, ?_⟩
  · intro hx
    exact Nat.find_min hex (by omega : j < Nat.find hex) hx
  · have h1 : s ^ (2 ^ j) * s ^ (2 ^ j) = s ^ (2 ^ Nat.find hex) := by
      rw [← pow_add, hj, pow_succ]
      congr 1
      ring
    rw [h1]
    exact hk₀T

theorem conjSubgroup_centralizer (g a : G) :
    conjSubgroup g (Subgroup.centralizer ({a} : Set G)) =
      Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext y
  have h1 : y ∈ conjSubgroup g (Subgroup.centralizer ({a} : Set G)) ↔
      g⁻¹ * y * g ∈ Subgroup.centralizer ({a} : Set G) := mem_conjSubgroup_iff
  rw [h1, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    calc (g * a * g⁻¹) * y = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by rw [h]
      _ = y * (g * a * g⁻¹) := by group
  · intro h
    calc a * (g⁻¹ * y * g) = g⁻¹ * ((g * a * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * a * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * y * g) * a := by group


theorem centralizer_ne_top_of_simple [IsSimpleGroup G] (hnc : ¬ ∀ a b : G, a * b = b * a) {c : G}
    (hc : c ≠ 1) : Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
  intro htop
  have hcen : c ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({c} : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp this c rfl).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact hc hcen
  · apply hnc
    intro a b
    have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm


theorem conj_eq_iff_mem_centralizer {t a a' : G} :
    a * t * a⁻¹ = a' * t * a'⁻¹ ↔ a⁻¹ * a' ∈ Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    calc t * (a⁻¹ * a') = a⁻¹ * (a * t * a⁻¹) * a' := by group
      _ = a⁻¹ * (a' * t * a'⁻¹) * a' := by rw [h]
      _ = (a⁻¹ * a') * t := by group
  · intro hc
    calc a * t * a⁻¹ = a * (t * (a⁻¹ * a') * (a⁻¹ * a')⁻¹) * a⁻¹ := by group
      _ = a * (((a⁻¹ * a') * t) * (a⁻¹ * a')⁻¹) * a⁻¹ := by rw [hc]
      _ = a' * t * a'⁻¹ := by group

structure Escape (T U : Subgroup G) (x : G) : Prop where
  two : IsPGroup 2 U
  le : T ≤ U
  mem : x ∈ U
  normalizes : x ∈ Subgroup.normalizer (T : Set G)
  not_mem : x ∉ T
  sq_mem : x * x ∈ T

namespace OddByQuat

variable {R S T U : Subgroup G} {t x : G}

section Criterion

variable [Finite G]

theorem T_sylow_H (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    IsSylow2Of T (Subgroup.centralizer ({t} : Set G)) :=
  (d.sylow_of_sylow_M hT).1

theorem S_le_T (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    S ≤ T := (d.sylow_of_sylow_M hT).2.1

omit [Finite G] in
theorem T_le_C (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    T ≤ Subgroup.centralizer ({t} : Set G) := fun _ hx => d.M_le_C (hT.1 hx)

theorem t_central (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    ∀ x ∈ T, t * x = x * t := (d.sylow_of_sylow_M hT).2.2.2

theorem inf_R_eq (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    T ⊓ R = S :=
  d.sylow.2.2 (T ⊓ R) inf_le_right (hT.2.1.to_le inf_le_left) (le_inf (d.S_le_T hT) d.S_le)

theorem normalizer_inf_eq (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G) =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (T : Set G) := by
  ext x
  constructor
  · rintro ⟨hm, hn⟩
    exact ⟨d.M_le_C hm, hn⟩
  · rintro ⟨hh, hn⟩
    refine ⟨?_, hn⟩
    show x ∈ Subgroup.normalizer (S : Set G)
    rw [← conjSubgroup_eq_self_iff, ← d.inf_R_eq hT, conjSubgroup_inf,
      conjSubgroup_eq_self_iff.mpr hn, conjSubgroup_eq_self_iff.mpr (d.normal hh)]


theorem conj_t_mem (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    {a : G} (ha : a ∈ Subgroup.normalizer (T : Set G)) :
    a * t * a⁻¹ ∈ T ∧ ∀ x ∈ T, (a * t * a⁻¹) * x = x * (a * t * a⁻¹) := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp ha t).mp (d.S_le_T hT d.t_mem), fun x hx => ?_⟩
  have hx' : a⁻¹ * x * a ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set G)).inv_mem ha) x).mp hx
    simpa using this
  have hc := d.t_central hT (a⁻¹ * x * a) hx'
  calc a * t * a⁻¹ * x = a * (t * (a⁻¹ * x * a)) * a⁻¹ := by group
    _ = a * ((a⁻¹ * x * a) * t) * a⁻¹ := by rw [hc]
    _ = x * (a * t * a⁻¹) := by group


end Criterion

section Escape

variable [Finite G]

omit [Finite G] in
theorem mul_comm_of_comm {a b y : G} (ha : a * y = y * a) (hb : b * y = y * b) :
    (a * b) * y = y * (a * b) := by
  calc (a * b) * y = a * (b * y) := mul_assoc a b y
    _ = a * (y * b) := by rw [hb]
    _ = (a * y) * b := (mul_assoc a y b).symm
    _ = (y * a) * b := by rw [ha]
    _ = y * (a * b) := mul_assoc y a b


theorem x_not_mem_C (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : x ∉ Subgroup.centralizer ({t} : Set G) := by
  intro hx
  have h := (d.T_sylow_H hT).2.2 (U ⊓ Subgroup.centralizer ({t} : Set G)) inf_le_right
    (e.two.to_le inf_le_left) (le_inf e.le (d.T_le_C hT))
  have hxU : x ∈ U ⊓ Subgroup.centralizer ({t} : Set G) := ⟨e.mem, hx⟩
  rw [h] at hxU
  exact e.not_mem hxU

theorem t₁_ne (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : x * t * x⁻¹ ≠ t := by
  intro h
  apply d.x_not_mem_C hT e
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  calc y * x = (x * y * x⁻¹) * x := by rw [h]
    _ = x * y := by group

omit [Finite G] in
theorem orderOf_t₁ (d : OddByQuat R S t) (x : G) : orderOf (x * t * x⁻¹) = 2 := by
  have := (MulAut.conj x).orderOf_eq t
  rw [MulAut.conj_apply] at this
  rw [this]
  exact d.t_ord

theorem conj_t₁ (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : x * (x * t * x⁻¹) * x⁻¹ = t := by
  have hxxT : (x * x) * t = t * (x * x) := (d.t_central hT (x * x) e.sq_mem).symm
  calc x * (x * t * x⁻¹) * x⁻¹ = (x * x) * t * (x * x)⁻¹ := by group
    _ = t := by rw [hxxT]; group

omit [Finite G] in
theorem T_le_normalizer_S₁ (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : T ≤ Subgroup.normalizer ((conjSubgroup x S : Subgroup G) : Set G) := by
  intro y hy
  rw [← conjSubgroup_eq_self_iff]
  have hy' : x⁻¹ * y * x ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set G)).inv_mem
      e.normalizes) y).mp hy
    simpa using this
  have h1 : conjSubgroup y (conjSubgroup x S) = conjSubgroup x (conjSubgroup (x⁻¹ * y * x) S) := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  rw [h1, conjSubgroup_eq_self_iff.mpr (hT.1 hy')]

theorem S₁_le_T (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : conjSubgroup x S ≤ T := by
  have := conjSubgroup_mono (g := x) (d.S_le_T hT)
  rwa [conjSubgroup_eq_self_iff.mpr e.normalizes] at this

omit [Finite G] in
theorem unique_S₁ (d : OddByQuat R S t) (x : G) :
    ∀ y ∈ conjSubgroup x S, orderOf y = 2 → y = x * t * x⁻¹ := by
  intro y hy hy2
  have hy' : x⁻¹ * y * x ∈ S := mem_conjSubgroup_iff.mp hy
  have h2 : orderOf (x⁻¹ * y * x) = 2 := by
    have := (MulAut.conj x⁻¹).orderOf_eq y
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this]
    exact hy2
  have h3 := d.unique _ hy' h2
  calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    _ = x * t * x⁻¹ := by rw [h3]

theorem inf_S_S₁ (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : S ⊓ conjSubgroup x S = ⊥ := by
  by_contra h
  have ht : t ∈ S ⊓ conjSubgroup x S := d.t_mem_of_ne_bot inf_le_left h
  exact d.t₁_ne hT e (d.unique_S₁ x t ht.2 d.t_ord).symm

theorem commute_S_S₁ (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : ∀ a ∈ S, ∀ b ∈ conjSubgroup x S, a * b = b * a := by
  intro a ha b hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ conjSubgroup x S := by
    have := (Subgroup.mem_normalizer_iff.mp
      (T_le_normalizer_S₁ hT e (d.S_le_T hT ha)) b).mp hb
    exact (conjSubgroup x S).mul_mem this ((conjSubgroup x S).inv_mem hb)
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ S := by
    have e' : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e']
    have := (Subgroup.mem_normalizer_iff.mp (hT.1 (d.S₁_le_T hT e hb)) a⁻¹).mp (S.inv_mem ha)
    exact S.mul_mem ha this
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ S ⊓ conjSubgroup x S := ⟨h2, h1⟩
  rw [d.inf_S_S₁ hT e, Subgroup.mem_bot] at h3
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]


omit [Finite G] in
theorem mem_W (e : Escape T U x) {w : G} (hw : w ∈ T ⊔ Subgroup.zpowers x) :
    w ∈ T ∨ ∃ y ∈ T, w = y * x := by
  have hxn : Subgroup.zpowers x ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.zpowers_le).mpr e.normalizes
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left T (Subgroup.zpowers x) hxn
  have h1 : w ∈ ((T ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := hw
  rw [hmul] at h1
  obtain ⟨y, hy, z, hz, rfl⟩ := h1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have key : ∀ k : ℤ, x ^ k ∈ T ∨ ∃ y' ∈ T, x ^ k = y' * x := by
    intro k
    induction k using Int.induction_on with
    | zero => exact Or.inl (by simp)
    | succ n ih =>
      rcases ih with h | ⟨y', hy', h⟩
      · exact Or.inr ⟨x ^ (n : ℤ), h, zpow_add_one x n⟩
      · left
        rw [zpow_add_one, h, mul_assoc]
        exact T.mul_mem hy' e.sq_mem
    | pred n ih =>
      rcases ih with h | ⟨y', hy', h⟩
      · right
        refine ⟨x ^ (-(n : ℤ)) * (x * x)⁻¹, T.mul_mem h (T.inv_mem e.sq_mem), ?_⟩
        rw [zpow_sub_one]
        group
      · left
        rw [zpow_sub_one, h]
        simpa using hy'
  rcases key k with h | ⟨y', hy', h⟩
  · exact Or.inl (T.mul_mem hy h)
  · exact Or.inr ⟨y * y', T.mul_mem hy hy', by rw [h]; group⟩

omit [Finite G] in
theorem relIndex_W (e : Escape T U x) : T.relIndex (T ⊔ Subgroup.zpowers x) = 2 := by
  have hxW : x ∈ T ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rw [Subgroup.relIndex, Subgroup.index_eq_card,
    Nat.card_eq_two_iff' (QuotientGroup.mk (1 : (T ⊔ Subgroup.zpowers x : Subgroup G)) :
      (T ⊔ Subgroup.zpowers x : Subgroup G) ⧸ T.subgroupOf (T ⊔ Subgroup.zpowers x))]
  refine ⟨QuotientGroup.mk ⟨x, hxW⟩, ?_, ?_⟩
  · intro h
    rw [QuotientGroup.eq] at h
    have h1 : (x⁻¹ * 1 : G) ∈ T := h
    simp only [mul_one] at h1
    exact e.not_mem (by simpa using T.inv_mem h1)
  · intro z hz
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective z
    rcases mem_W e hw with h | ⟨y, hy, rfl⟩
    · exfalso
      apply hz
      rw [QuotientGroup.eq]
      show ((w⁻¹ * 1 : G)) ∈ T
      simpa using T.inv_mem h
    · rw [QuotientGroup.eq]
      show ((y * x)⁻¹ * x : G) ∈ T
      have h1 : (y * x)⁻¹ * x = x⁻¹ * y⁻¹ * x := by group
      rw [h1]
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set G)).inv_mem
        e.normalizes) y⁻¹).mp (T.inv_mem hy)
      simpa using this

omit [Finite G] in
theorem card_W (e : Escape T U x) :
    Nat.card (T ⊔ Subgroup.zpowers x : Subgroup G) = 2 * Nat.card T := by
  have h := Subgroup.card_mul_index (T.subgroupOf (T ⊔ Subgroup.zpowers x))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (le_sup_left : T ≤ T ⊔ Subgroup.zpowers x)).toEquiv] at h
  have h2 := relIndex_W e
  rw [Subgroup.relIndex] at h2
  rw [h2] at h
  rw [← h]
  ring

omit [Finite G] in
theorem W_two (e : Escape T U x) : IsPGroup 2 (T ⊔ Subgroup.zpowers x : Subgroup G) :=
  e.two.to_le (sup_le e.le ((Subgroup.zpowers_le).mpr e.mem))


theorem c_central (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) :
    T ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G) := by
  have hT₁ := d.conj_t_mem hT e.normalizes
  have hcT : ∀ y ∈ T, y * (t * (x * t * x⁻¹)) = (t * (x * t * x⁻¹)) * y := fun y hy =>
    (mul_comm_of_comm (d.t_central hT y hy) (hT₁.2 y hy)).symm
  have hcomm : (x * t * x⁻¹) * t = t * (x * t * x⁻¹) :=
    (d.t_central hT _ hT₁.1).symm
  refine sup_le (fun y hy => ?_) ((Subgroup.zpowers_le).mpr ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hcT y hy).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hx1 := d.conj_t₁ hT e
    have hxc : x * (t * (x * t * x⁻¹)) * x⁻¹ = t * (x * t * x⁻¹) := by
      calc x * (t * (x * t * x⁻¹)) * x⁻¹ = (x * t * x⁻¹) * (x * (x * t * x⁻¹) * x⁻¹) := by group
        _ = (x * t * x⁻¹) * t := by rw [hx1]
        _ = t * (x * t * x⁻¹) := hcomm
    exact (mul_inv_eq_iff_eq_mul.mp hxc).symm

theorem orderOf_c (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : orderOf (t * (x * t * x⁻¹)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁ := d.conj_t_mem hT e.normalizes
  have hcomm : (x * t * x⁻¹) * t = t * (x * t * x⁻¹) := (d.t_central hT _ hT₁.1).symm
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [d.t_ord, pow_two] at this
  have ht₁2 : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
    calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  apply orderOf_eq_prime
  · rw [pow_two]
    calc t * (x * t * x⁻¹) * (t * (x * t * x⁻¹)) = t * ((x * t * x⁻¹) * t) * (x * t * x⁻¹) := by
          group
      _ = t * (t * (x * t * x⁻¹)) * (x * t * x⁻¹) := by rw [hcomm]
      _ = (t * t) * ((x * t * x⁻¹) * (x * t * x⁻¹)) := by group
      _ = 1 := by rw [ht2, ht₁2]; group
  · intro h
    apply d.t₁_ne hT e
    have h1 : x * t * x⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right ht2


end Escape

end OddByQuat

end CFSG.ClassicalInvolution
