
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4RadX0Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Cfg

@[expose] public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4
open scoped commutatorElement

theorem map_cm_of_mem_normalizer {Y : Type*} [Group Y] {V : Subgroup Y} {n : Y}
    (hn : n ∈ Subgroup.normalizer (V : Set Y)) : V.map (cm n) = V := by
  ext z
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hn v).1 hv
  · intro hz
    refine ⟨n⁻¹ * z * n, ?_, by simp [cm_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) z).1 hz
    simpa using this

theorem map_cm_map_cm {Y : Type*} [Group Y] (a b : Y) (V : Subgroup Y) :
    (V.map (cm a)).map (cm b) = V.map (cm (b * a)) := by
  rw [Subgroup.map_map, cm_comp]

theorem map_cm_inv_map_cm {Y : Type*} [Group Y] (a : Y) (V : Subgroup Y) :
    (V.map (cm a)).map (cm a⁻¹) = V := by
  rw [Subgroup.map_map, cm_comp_inv, Subgroup.map_id]

theorem radV_map_cm {Y : Type*} [Group Y] (m x : Y) {V : Subgroup Y} (h : RadV x V) :
    RadV (cm m x) (V.map (cm m)) := by
  obtain ⟨h1, h2⟩ := h
  have hf := cm_injective m
  unfold RadV
  rw [radOf_map_cm]
  have hc : Subgroup.centralizer (((radOf V).map (cm m) : Subgroup Y) : Set Y) =
      (Subgroup.centralizer (radOf V : Set Y)).map (cm m) := by
    rw [Subgroup.coe_map]
    exact centralizer_image_cm m _
  have hx : Subgroup.centralizer ({cm m x} : Set Y) =
      (Subgroup.centralizer ({x} : Set Y)).map (cm m) := by
    rw [← centralizer_image_cm, Set.image_singleton]
  refine ⟨?_, ?_⟩
  · rw [hc]
    exact Subgroup.map_mono h1
  · rw [hx, ← Subgroup.map_inf _ _ (cm m) hf, Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact h2

theorem radV_of_zpow {Y : Type*} [Group Y] [Finite Y] {x : Y} {V : Subgroup Y} (k : ℤ)
    (h : RadV (x ^ k) V) : RadV x V := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
  have hle : radOf V ⊓ Subgroup.centralizer ({x} : Set Y) ≤
      radOf V ⊓ Subgroup.centralizer ({x ^ k} : Set Y) := by
    refine inf_le_inf_left _ ?_
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hxc : Commute x c := hc x rfl
    exact (hxc.zpow_left k).eq
  have hd := Subgroup.relIndex_dvd_of_le_left (radOf V) hle
  have hne : (radOf V ⊓ Subgroup.centralizer ({x} : Set Y)).relIndex (radOf V) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd

@[expose] def ClassRad {Y : Type*} [Group Y] (V : Subgroup Y) : Prop :=
  ∃ y ∈ Subgroup.normalizer (V : Set Y), orderOf y = 5 ∧ RadV y V

theorem classRad_map_cm {Y : Type*} [Group Y] (m : Y) {V : Subgroup Y} (h : ClassRad V) :
    ClassRad (V.map (cm m)) := by
  obtain ⟨y, hy, hy5, hR⟩ := h
  refine ⟨cm m y, ?_, ?_, radV_map_cm m y hR⟩
  · have e := normalizer_map_equiv_eq (MulAut.conj m) V
    change cm m y ∈ Subgroup.normalizer ((V.map (MulAut.conj m).toMonoidHom : Subgroup Y) : Set Y)
    rw [e]
    exact ⟨y, hy, rfl⟩
  · have h5 := (MulAut.conj m).orderOf_eq y
    rw [MulAut.conj_apply] at h5
    rw [cm_apply, h5]
    exact hy5

theorem radV_of_classRad {Y : Type} [Group Y] [Finite Y] (hY : ¬ 5 ^ 2 ∣ Nat.card Y)
    {V : Subgroup Y} (h : ClassRad V) {y' : Y} (hy' : y' ∈ Subgroup.normalizer (V : Set Y))
    (h5 : orderOf y' = 5) : RadV y' V := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy, hy5, hR⟩ := h
  have hP : ¬ 5 ^ 2 ∣ Nat.card (Subgroup.normalizer (V : Set Y)) := fun hd =>
    hY (hd.trans (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨n, hn, k, hk⟩ := Kc3J4.exists_conj_of_orderOf_prime (p := 5) hP hy' hy h5 hy5
  have h1 : RadV (cm n⁻¹ y) (V.map (cm n⁻¹)) := radV_map_cm n⁻¹ y hR
  rw [map_cm_of_mem_normalizer (inv_mem hn)] at h1
  have h2 : cm n⁻¹ y = y' ^ k := by
    rw [cm_apply, hk]
    group
  rw [h2] at h1
  exact radV_of_zpow k h1

theorem classRad_of_centralizer {Y : Type*} [Group Y] [Finite Y] {V : Subgroup Y} {y : Y}
    (hy : y ∈ Subgroup.normalizer (V : Set Y)) (h5 : orderOf y = 5)
    (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hU : IsPGroup 2 (Subgroup.centralizer (V : Set Y)))
    (hidx : 16 < (Subgroup.centralizer (V : Set Y) ⊓
      Subgroup.centralizer ({y} : Set Y)).relIndex (Subgroup.centralizer (V : Set Y))) :
    ClassRad V :=
  ⟨y, hy, h5, radV_of_centralizer y hab hU hidx⟩

@[expose] def NoNonHBlockAt {Y : Type} [Group Y] (Hy : Subgroup Y) (V : Subgroup Y) : Prop :=
  ∀ L : Subgroup Y, D5Plus L → ⁅L, L⁆ = L → pCoreOf 2 L = V →
    (∃ g : Y, L ≤ Hy.map (MulAut.conj g).toMonoidHom) ∨
      ∃ y : Y, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l

theorem noNonHBlockAt_map_cm {Y : Type} [Group Y] (Hy : Subgroup Y) (m : Y) {V : Subgroup Y}
    (h : NoNonHBlockAt Hy V) : NoNonHBlockAt Hy (V.map (cm m)) := by
  intro L hL hLp hP
  have hL0 : D5Plus (L.map (cm m⁻¹)) := d5Plus_map (cm m⁻¹) (cm_injective _) hL
  have hLp0 : ⁅L.map (cm m⁻¹), L.map (cm m⁻¹)⁆ = L.map (cm m⁻¹) := by
    rw [← Subgroup.map_commutator, hLp]
  have hP0 : pCoreOf 2 (L.map (cm m⁻¹)) = V := by
    have h1 : pCoreOf 2 (L.map (cm m⁻¹)) = (pCoreOf 2 L).map (cm m⁻¹) :=
      CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj m⁻¹) L
    rw [h1, hP, map_cm_inv_map_cm]
  rcases h _ hL0 hLp0 hP0 with ⟨g, hg⟩ | ⟨y, hy2, hyc⟩
  · refine Or.inl ⟨m * g, fun l hl => ?_⟩
    obtain ⟨a, ha, hal⟩ := hg (Subgroup.mem_map.2 ⟨l, hl, rfl⟩)
    have h1 : g * a * g⁻¹ = m⁻¹ * l * m := by simpa [MulAut.conj_apply, cm_apply] using hal
    refine ⟨a, ha, ?_⟩
    show (m * g) * a * (m * g)⁻¹ = l
    calc (m * g) * a * (m * g)⁻¹ = m * (g * a * g⁻¹) * m⁻¹ := by group
      _ = m * (m⁻¹ * l * m) * m⁻¹ := by rw [h1]
      _ = l := by group
  · refine Or.inr ⟨m * y * m⁻¹, ?_, fun l hl => ?_⟩
    · have h5 := (MulAut.conj m).orderOf_eq y
      rw [MulAut.conj_apply] at h5
      rw [h5]
      exact hy2
    · have h1 := hyc (m⁻¹ * l * m) (Subgroup.mem_map.2 ⟨l, hl, by simp [cm_apply]⟩)
      calc l * (m * y * m⁻¹) = m * ((m⁻¹ * l * m) * y) * m⁻¹ := by group
        _ = m * (y * (m⁻¹ * l * m)) * m⁻¹ := by rw [h1]
        _ = (m * y * m⁻¹) * l := by group

theorem noNonHBlockAt_of_normalizer_le {Y : Type} [Group Y] [Finite Y] {Hy V : Subgroup Y}
    (g : Y) (h : Subgroup.normalizer (V : Set Y) ≤ Hy.map (MulAut.conj g).toMonoidHom) :
    NoNonHBlockAt Hy V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro L _ _ hP
  refine Or.inl ⟨g, fun l hl => h ?_⟩
  have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl
  rwa [hP] at this


@[expose] def FpfV {Y : Type} [Group Y] (V : Subgroup Y) : Prop :=
  Nat.card V = 16 ∧ (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) ∧ (∀ a ∈ V, a * a = 1) ∧
    ∃ x ∈ Subgroup.normalizer (V : Set Y), orderOf x = 5 ∧ ∀ v ∈ V, x * v = v * x → v = 1


open CFSG.QuasithinUnique.A5.Delta5 Equiv in
theorem fpfV_of_d5Core {G : Type} [Group G] [Finite G] {L : Subgroup G} (hD : D5Core L) :
    FpfV (pCoreOf 2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨V, hVL, hV2, hLV, α, hα, hαV, β, hβ⟩ := hD
  have hPV : pCoreOf 2 L = V := by
    apply le_antisymm
    · exact le_Q_of_normal_two α hα hαV (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL hLV hV2
  rw [hPV]
  have hconjV : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V := fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.1 (hLV hl) v).1 hv
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have h : β ⟨a, ha⟩ * β ⟨b, hb⟩ = β ⟨b, hb⟩ * β ⟨a, ha⟩ := mul_comm _ _
    have h' : (⟨a, ha⟩ : ↥V) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      β.injective (by rw [map_mul, map_mul]; exact h)
    exact congrArg Subtype.val h'
  have hVsq : ∀ a ∈ V, a * a = 1 := by
    intro a ha
    have h : β ⟨a, ha⟩ * β ⟨a, ha⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul]
      generalize Multiplicative.toAdd (β ⟨a, ha⟩) = u
      apply Subtype.ext
      funext i
      exact zmod_two_self_add (u.1 i)
    have h' : (⟨a, ha⟩ : ↥V) * ⟨a, ha⟩ = 1 := β.injective (by rw [map_mul, h, map_one])
    exact congrArg Subtype.val h'
  have hfixvec : ∀ (l : ↥L) (v : ↥V), (l : G) * v = v * l →
      vact ((α l : Alt5) : Perm (Fin 5)) (Multiplicative.toAdd (β v)) =
        Multiplicative.toAdd (β v) := by
    intro l v h
    refine (hβ l v v ?_).symm
    show (v : G) = (l : G) * (v : G) * (l : G)⁻¹
    rw [h]
    group
  obtain ⟨l0, hl0⟩ := hα a0'
  have ha5 : a0' ^ 5 = 1 := Subtype.ext a0_pow_five
  have hl05 : l0 ^ 5 * l0 ^ 5 = 1 := by
    have h1 : α (l0 ^ 5) = 1 := by rw [map_pow, hl0, ha5]
    have h2 := hVsq _ ((hαV _).1 h1)
    exact Subtype.ext (by simpa using h2)
  have hl010 : l0 ^ 10 = 1 := by
    rw [show 10 = 5 + 5 from rfl, pow_add]
    exact hl05
  have hαx : α (l0 ^ 6) = a0' := by
    rw [map_pow, hl0, show 6 = 5 + 1 from rfl, pow_add, ha5, one_mul, pow_one]
  have hx5 : (l0 ^ 6) ^ 5 = 1 := by
    calc (l0 ^ 6) ^ 5 = (l0 ^ 10) ^ 3 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [hl010, one_pow]
  have hx1 : l0 ^ 6 ≠ 1 := by
    intro h
    rw [h, map_one] at hαx
    exact a0_ne_one (congrArg Subtype.val hαx.symm)
  have hordx : orderOf ((l0 ^ 6 : ↥L) : G) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx5 hx1
  refine ⟨card_V β, hVcomm, hVsq, ((l0 ^ 6 : ↥L) : G), hLV (l0 ^ 6).2, hordx, ?_⟩
  intro v hv hcomm
  have h1 := hfixvec (l0 ^ 6) ⟨v, hv⟩ hcomm
  rw [hαx] at h1
  have h2 : (Multiplicative.toAdd (β ⟨v, hv⟩)).1 = 0 :=
    a0_fixed_zero _ ((mem_evenWeight_iff _).1 (Multiplicative.toAdd (β ⟨v, hv⟩)).2)
      (congrArg Subtype.val h1)
  have h3 : β ⟨v, hv⟩ = 1 := Multiplicative.toAdd.injective (Subtype.ext h2)
  have h4 : (⟨v, hv⟩ : ↥V) = 1 := β.injective (by rw [h3, map_one])
  exact congrArg Subtype.val h4

@[expose] def J4VVerdict : Prop :=
  ∀ V : Subgroup ↥J, FpfV V → ClassRad V ∨ NoNonHBlockAt Hj V

theorem verdict_of_list (lst : List (Subgroup ↥J))
    (hcl : ∀ V : Subgroup ↥J, FpfV V → ∃ V' ∈ lst, ∃ g : ↥J, V = V'.map (cm g))
    (hdec : ∀ V' ∈ lst, ClassRad V' ∨ NoNonHBlockAt Hj V') : J4VVerdict := by
  intro V hV
  obtain ⟨V', hV', g, rfl⟩ := hcl V hV
  rcases hdec V' hV' with h | h
  · exact Or.inl (classRad_map_cm g h)
  · exact Or.inr (noNonHBlockAt_map_cm Hj g h)

end CFSG.QuasithinUnique.A5
