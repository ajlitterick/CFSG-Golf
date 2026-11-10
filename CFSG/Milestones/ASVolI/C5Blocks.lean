module

public import CFSG.Milestones.ASVolI.C5

public section

namespace CFSG.ASVolI

open CFSG.Open


section


end

@[expose] def burnsideC5h_p1_UMaxIn {G : Type*} [Group G] (K P : Subgroup G) : Prop :=
  ∃ B : Subgroup G, B < K ∧ P ≤ B ∧ ∀ Y : Subgroup G, P ≤ Y → Y < K → Y ≤ B

theorem burnsideC5h_p1_umaxIn_orderIso {G : Type*} [Group G] (e : Subgroup G ≃o Subgroup G)
    {K P : Subgroup G} (h : burnsideC5h_p1_UMaxIn K P) :
    burnsideC5h_p1_UMaxIn (e K) (e P) := by
  obtain ⟨B, hBK, hPB, hmax⟩ := h
  refine ⟨e B, e.strictMono hBK, e.monotone hPB, fun Y hPY hYK => ?_⟩
  have h1 : P ≤ e.symm Y := e.le_symm_apply.mpr hPY
  have h2 : e.symm Y < K := by
    have := e.symm.strictMono hYK
    rwa [OrderIso.symm_apply_apply] at this
  exact e.symm_apply_le.mp (hmax _ h1 h2)


theorem burnsideC5h_p1_umaxIn_top_orderIso {Γ : Type*} [Group Γ] (e : Subgroup Γ ≃o Subgroup Γ)
    {P : Subgroup Γ} (h : burnsideC5h_p1_UMaxIn ⊤ P) : burnsideC5h_p1_UMaxIn ⊤ (e P) := by
  have := burnsideC5h_p1_umaxIn_orderIso e h
  rwa [map_top] at this

theorem burnsideC5h_p1_umax_of_surjective {Γ Q : Type*} [Group Γ] [Group Q] (π : Γ →* Q)
    (hπ : Function.Surjective π) {S : Subgroup Γ} (hker : π.ker ≤ S)
    (h : burnsideC5h_p1_UMaxIn ⊤ (S.map π)) : burnsideC5h_p1_UMaxIn ⊤ S := by
  obtain ⟨B, hB, hSB, hmax⟩ := h
  refine ⟨B.comap π, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne le_top fun h => hB.ne ?_
    rw [eq_top_iff]
    intro q _
    obtain ⟨g, rfl⟩ := hπ q
    have : g ∈ B.comap π := h ▸ Subgroup.mem_top g
    exact this
  · intro s hs
    exact hSB ⟨s, hs, rfl⟩
  · intro Y hSY hY
    have hY' : Y.map π < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => hY.ne ?_
      rw [eq_top_iff]
      intro g _
      have h1 : π g ∈ Y.map π := h ▸ Subgroup.mem_top _
      obtain ⟨y, hy, hyg⟩ := h1
      have h2 : y⁻¹ * g ∈ π.ker := by simp [MonoidHom.mem_ker, hyg]
      have h3 := hSY (hker h2)
      simpa using Y.mul_mem hy h3
    have h4 := hmax _ (Subgroup.map_mono hSY) hY'
    intro y hy
    exact h4 ⟨y, hy, rfl⟩

theorem burnsideC5h_p1_umaxIn_of_subtype {G : Type*} [Group G] {K P : Subgroup G} (hPK : P ≤ K)
    (h : burnsideC5h_p1_UMaxIn (⊤ : Subgroup ↥K) (P.subgroupOf K)) :
    burnsideC5h_p1_UMaxIn K P := by
  obtain ⟨B', hB', hPB', hmax⟩ := h
  refine ⟨B'.map K.subtype, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_subtype_le B') fun h => hB'.ne ?_
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ B'.map K.subtype := by rw [h]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · rw [← Subgroup.map_subgroupOf_eq_of_le hPK]
    exact Subgroup.map_mono hPB'
  · intro Y hPY hYK
    have hY' : Y.subgroupOf K < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => hYK.ne ?_
      exact le_antisymm hYK.le (Subgroup.subgroupOf_eq_top.mp h)
    have hPY' : P.subgroupOf K ≤ Y.subgroupOf K := fun x hx => hPY hx
    have h4 := hmax _ hPY' hY'
    intro y hy
    exact ⟨⟨y, hYK.le hy⟩, h4 hy, rfl⟩


section SL2

variable {F : Type} [Field F]

@[expose] def burnsideC5h_p1_sl (a b c d : F) (h : a * d - b * c = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

theorem burnsideC5h_p1_coe_sl (a b c d : F) (h : a * d - b * c = 1) :
    (burnsideC5h_p1_sl a b c d h : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := rfl

@[expose] def burnsideC5h_p1_utri (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  burnsideC5h_p1_sl 1 t 0 1 (by simp)

@[expose] def burnsideC5h_p1_ltri (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  burnsideC5h_p1_sl 1 0 t 1 (by simp)

theorem burnsideC5h_p1_coe_utri (t : F) :
    (burnsideC5h_p1_utri t : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

theorem burnsideC5h_p1_coe_ltri (t : F) :
    (burnsideC5h_p1_ltri t : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t, 1] := rfl

theorem burnsideC5h_p1_utri_mul (s t : F) :
    burnsideC5h_p1_utri s * burnsideC5h_p1_utri t = burnsideC5h_p1_utri (s + t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, burnsideC5h_p1_coe_utri, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem burnsideC5h_p1_utri_zero : burnsideC5h_p1_utri (0 : F) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [burnsideC5h_p1_coe_utri]

@[expose] def burnsideC5h_p1_utriHom (F : Type) [Field F] :
    Multiplicative F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun t := burnsideC5h_p1_utri (Multiplicative.toAdd t)
  map_one' := burnsideC5h_p1_utri_zero
  map_mul' s t := by
    simp only [toAdd_mul]
    exact (burnsideC5h_p1_utri_mul _ _).symm

theorem burnsideC5h_p1_utriHom_apply (t : Multiplicative F) :
    burnsideC5h_p1_utriHom F t = burnsideC5h_p1_utri (Multiplicative.toAdd t) := rfl

theorem burnsideC5h_p1_utriHom_injective : Function.Injective (burnsideC5h_p1_utriHom F) := by
  intro s t h
  rw [burnsideC5h_p1_utriHom_apply, burnsideC5h_p1_utriHom_apply] at h
  have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [burnsideC5h_p1_coe_utri] using h1

@[expose] def burnsideC5h_p1_U (F : Type) [Field F] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
  (burnsideC5h_p1_utriHom F).range

@[expose] def burnsideC5h_p1_B (F : Type) [Field F] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ha]

theorem burnsideC5h_p1_utri_mem_U (t : F) : burnsideC5h_p1_utri t ∈ burnsideC5h_p1_U F :=
  ⟨Multiplicative.ofAdd t, rfl⟩

theorem burnsideC5h_p1_U_le_B : burnsideC5h_p1_U F ≤ burnsideC5h_p1_B F := by
  rintro _ ⟨t, rfl⟩
  show (burnsideC5h_p1_utri (Multiplicative.toAdd t) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  simp [burnsideC5h_p1_coe_utri]

theorem burnsideC5h_p1_B_lt_top : burnsideC5h_p1_B F < ⊤ := by
  refine lt_of_le_of_ne le_top fun h => ?_
  have h1 : burnsideC5h_p1_ltri (1 : F) ∈ burnsideC5h_p1_B F := h ▸ Subgroup.mem_top _
  have h2 : (burnsideC5h_p1_ltri (1 : F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := h1
  simp [burnsideC5h_p1_coe_ltri] at h2

theorem burnsideC5h_p1_sl2_eq_top {Y : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hU : ∀ t : F, burnsideC5h_p1_utri t ∈ Y) (hL : ∀ t : F, burnsideC5h_p1_ltri t ∈ Y) :
    Y = ⊤ := by
  have key : ∀ {a b c d : F} (hdet : a * d - b * c = 1), c ≠ 0 →
      burnsideC5h_p1_sl a b c d hdet ∈ Y := by
    intro a b c d hdet hc
    have hb : b = (a * d - 1) / c := by
      field_simp
      linear_combination (-1 : F) * hdet
    subst hb
    have h : burnsideC5h_p1_sl a ((a * d - 1) / c) c d hdet =
        burnsideC5h_p1_utri ((a - 1) / c) * burnsideC5h_p1_ltri c *
          burnsideC5h_p1_utri ((d - 1) / c) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, burnsideC5h_p1_coe_utri,
          burnsideC5h_p1_coe_ltri, burnsideC5h_p1_coe_sl, Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp <;> ring
    rw [h]
    exact Y.mul_mem (Y.mul_mem (hU _) (hL _)) (hU _)
  rw [eq_top_iff]
  intro g _
  refine Matrix.SpecialLinearGroup.fin_two_induction (fun g => g ∈ Y) ?_ g
  intro a b c d hdet
  change burnsideC5h_p1_sl a b c d hdet ∈ Y
  by_cases hc : c = 0
  · subst hc
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hdet
    have hdet' : a * (b + d) - b * a = 1 := by linear_combination hdet
    have h1 := key hdet' ha
    have h : burnsideC5h_p1_sl a b 0 d hdet =
        burnsideC5h_p1_ltri (-1) * burnsideC5h_p1_sl a b a (b + d) hdet' := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, burnsideC5h_p1_coe_ltri,
          burnsideC5h_p1_coe_sl, Matrix.mul_apply, Fin.sum_univ_two]
    rw [h]
    exact Y.mul_mem (hL _) h1
  · exact key hdet hc

theorem burnsideC5h_p1_sl2_ltri_mem {Y : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hU : ∀ t : F, burnsideC5h_p1_utri t ∈ Y) {a b c d : F} (hdet : a * d - b * c = 1)
    (hc : c ≠ 0) (hy : burnsideC5h_p1_sl a b c d hdet ∈ Y) :
    ∀ z : F, burnsideC5h_p1_ltri z ∈ Y := by
  have hb : b = (a * d - 1) / c := by
    field_simp
    linear_combination (-1 : F) * hdet
  subst hb
  have hwdet : (0 : F) * 0 - (-c⁻¹) * c = 1 := by field_simp; ring
  have hwY : burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet ∈ Y := by
    have h : burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet =
        burnsideC5h_p1_utri (-a / c) * burnsideC5h_p1_sl a ((a * d - 1) / c) c d hdet *
          burnsideC5h_p1_utri (-d / c) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, burnsideC5h_p1_coe_utri,
          burnsideC5h_p1_coe_sl, Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp <;> ring
    rw [h]
    exact Y.mul_mem (Y.mul_mem (hU _) hy) (hU _)
  intro z
  have hcomm : burnsideC5h_p1_ltri z * burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet =
      burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet * burnsideC5h_p1_utri (-z / c ^ 2) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, burnsideC5h_p1_coe_utri,
        burnsideC5h_p1_coe_ltri, burnsideC5h_p1_coe_sl, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring
  have h2 : burnsideC5h_p1_ltri z = burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet *
      burnsideC5h_p1_utri (-z / c ^ 2) * (burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet)⁻¹ :=
    eq_mul_inv_of_mul_eq hcomm
  rw [h2]
  exact Y.mul_mem (Y.mul_mem hwY (hU _)) (Y.inv_mem hwY)

theorem burnsideC5h_p1_sl2_eq_top_of_not_le {Y : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hUY : burnsideC5h_p1_U F ≤ Y) (hY : ¬ Y ≤ burnsideC5h_p1_B F) : Y = ⊤ := by
  have hU : ∀ t : F, burnsideC5h_p1_utri t ∈ Y := fun t => hUY (burnsideC5h_p1_utri_mem_U t)
  obtain ⟨y, hyY, hyB⟩ := SetLike.not_le_iff_exists.mp hY
  refine burnsideC5h_p1_sl2_eq_top hU ?_
  revert hyY hyB
  refine Matrix.SpecialLinearGroup.fin_two_induction
    (fun y => y ∈ Y → y ∉ burnsideC5h_p1_B F → ∀ z : F, burnsideC5h_p1_ltri z ∈ Y) ?_ y
  intro a b c d hdet hy hyB
  have hc : c ≠ 0 := fun h => hyB (by
    show (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp [h])
  exact burnsideC5h_p1_sl2_ltri_mem hU hdet hc hy

theorem burnsideC5h_p1_umax_U : burnsideC5h_p1_UMaxIn ⊤ (burnsideC5h_p1_U F) :=
  ⟨burnsideC5h_p1_B F, burnsideC5h_p1_B_lt_top, burnsideC5h_p1_U_le_B, fun Y hUY hY => by
    by_contra hYB
    exact hY.ne (burnsideC5h_p1_sl2_eq_top_of_not_le hUY hYB)⟩

theorem burnsideC5h_p1_sl2_card (F : Type) [Field F] [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  have h := Matrix.card_SL_mul_card_units (n := Fin 2) (R := F)
  rw [Matrix.card_GL_field, Nat.card_units, Nat.card_eq_fintype_card (α := F)] at h
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 2 := ⟨Fintype.card F - 2, by omega⟩
  rw [hm] at h ⊢
  have e1 : (m + 2) ^ 2 - 1 = (m + 1) * (m + 3) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (m + 2) ^ 2 - (m + 2) = (m + 2) * (m + 1) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : m + 2 - 1 = m + 1 := by omega
  rw [e1, e2, e3] at h
  rw [e1]
  have h' : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * (m + 1) =
      ((m + 2) * ((m + 1) * (m + 3))) * (m + 1) := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) h'

theorem burnsideC5h_p1_isSylow_U [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) :
    CFSG.QuasithinUnique.IsSylowTwoOf (burnsideC5h_p1_U F) ⊤ := by
  have hcardU : Nat.card (burnsideC5h_p1_U F) = Fintype.card F := by
    have e := MonoidHom.ofInjective (burnsideC5h_p1_utriHom_injective (F := F))
    calc Nat.card (burnsideC5h_p1_U F) = Nat.card (Multiplicative F) :=
          Nat.card_congr e.toEquiv.symm
      _ = Nat.card F := Nat.card_congr Multiplicative.toAdd
      _ = Fintype.card F := Nat.card_eq_fintype_card
  refine ⟨le_top, IsPGroup.of_card (n := n) (by rw [hcardU, hF]), ?_⟩
  have hmul := Subgroup.card_mul_index (burnsideC5h_p1_U F)
  rw [hcardU, burnsideC5h_p1_sl2_card] at hmul
  have hq0 : 0 < Fintype.card F := Fintype.card_pos
  have hidx : (burnsideC5h_p1_U F).index = Fintype.card F ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left hq0 hmul
  change ¬ 2 ∣ (burnsideC5h_p1_U F).relIndex ⊤
  rw [Subgroup.relIndex_top_right, hidx, hF]
  have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  have h3 : 0 < (2 ^ n) ^ 2 := by positivity
  omega

theorem burnsideC5h_p1_umax_sl2 [Fintype F] {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) : burnsideC5h_p1_UMaxIn ⊤ S := by
  have hU := burnsideC5h_p1_isSylow_U (F := F) hn hF
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ :=
    ⟨le_top, hS, by
      change ¬ 2 ∣ S.relIndex ⊤
      rwa [Subgroup.relIndex_top_right]⟩
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hU hSyl
  rw [hg]
  exact burnsideC5h_p1_umaxIn_top_orderIso _ burnsideC5h_p1_umax_U

end SL2

section Alt5


end Alt5

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_p1_umaxIn_of_quotient {G Q : Type} [Group G] [Finite G] [Group Q]
    {K P : Subgroup G} (hP : IsSylowTwoOf P K) (α : ↥K →* Q) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K)
    (hQ : ∀ S : Subgroup Q, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S) :
    burnsideC5h_p1_UMaxIn K P := by
  have hPK : P ≤ K := hP.1
  have hpc : pCoreOf 2 K ≤ P := B6.pCoreOf_two_le_of_isSylowTwoOf hP
  have hkerP : α.ker ≤ P.subgroupOf K := by
    intro x hx
    rw [hker] at hx
    exact hpc ⟨x, hx, rfl⟩
  have hP2 : IsPGroup 2 ↥(P.subgroupOf K) :=
    hP.2.1.comap_of_injective K.subtype K.subtype_injective
  have hS2 : IsPGroup 2 ↥((P.subgroupOf K).map α) := hP2.map α
  have hSi : ¬ 2 ∣ ((P.subgroupOf K).map α).index := by
    rw [Subgroup.index_map, sup_eq_left.mpr hkerP, MonoidHom.range_eq_top.mpr hα,
      Subgroup.index_top, mul_one]
    exact hP.2.2
  exact burnsideC5h_p1_umaxIn_of_subtype hPK
    (burnsideC5h_p1_umax_of_surjective α hα hkerP (hQ _ hS2 hSi))


open CFSG.Quasithin CFSG.QuasithinUnique in
open scoped Pointwise in
theorem burnsideC5h_p1_uniqueMax_sup {G : Type} [Group G] [Finite G] {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hU : burnsideC5h_p1_UMaxIn A (A ⊓ B)) :
    ∃ N : Subgroup G, CFSG.Quasithin.IsUniqueMaxOver (A ⊔ B) B N := by
  obtain ⟨B₀, hB₀A, hPB₀, hmax⟩ := hU
  have hconj : ∀ x ∈ B, conjByElt x B₀ ≤ B₀ := by
    intro x hx
    have hxA : conjByElt x A = A := C2Eleven.mem_normalizer_iff_conjByElt.mp (hBA hx)
    have hxB : conjByElt x B = B := C2Eleven.mem_normalizer_iff_conjByElt.mp
      (Subgroup.le_normalizer hx)
    have hxP : conjByElt x (A ⊓ B) = A ⊓ B := by
      have e : conjByElt x (A ⊓ B) = conjByElt x A ⊓ conjByElt x B :=
        Subgroup.map_inf A B (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
      rw [e, hxA, hxB]
    have hlt : conjByElt x B₀ < A := by
      have := (MulEquiv.mapSubgroup (MulAut.conj x)).strictMono hB₀A
      change conjByElt x B₀ < conjByElt x A at this
      rwa [hxA] at this
    have hPle : A ⊓ B ≤ conjByElt x B₀ := by
      calc A ⊓ B = conjByElt x (A ⊓ B) := hxP.symm
        _ ≤ conjByElt x B₀ := Subgroup.map_mono hPB₀
    exact hmax _ hPle hlt
  have hnorm : B ≤ Subgroup.normalizer (B₀ : Set G) := by
    intro x hx
    rw [C2Eleven.mem_normalizer_iff_conjByElt]
    refine le_antisymm (hconj x hx) ?_
    have h1 := hconj x⁻¹ (B.inv_mem hx)
    have h2 : conjByElt x (conjByElt x⁻¹ B₀) = B₀ := by
      rw [← C2Eleven.conjByElt_mul, mul_inv_cancel, C2Eleven.conjByElt_one]
    calc B₀ = conjByElt x (conjByElt x⁻¹ B₀) := h2.symm
      _ ≤ conjByElt x B₀ := Subgroup.map_mono h1
  have hsup : ∀ z ∈ A ⊔ B, ∃ b ∈ B, ∃ a ∈ A, z = b * a := by
    intro z hz
    have hset : ((B ⊔ A : Subgroup G) : Set G) = (B : Set G) * (A : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right B A hBA
    have hz' : z ∈ ((B ⊔ A : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hz
    rw [hset] at hz'
    obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.mp hz'
    exact ⟨b, hb, a, ha, rfl⟩
  have hsup0 : ∀ z ∈ B₀ ⊔ B, ∃ b ∈ B, ∃ c ∈ B₀, z = b * c := by
    intro z hz
    have hset : ((B ⊔ B₀ : Subgroup G) : Set G) = (B : Set G) * (B₀ : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right B B₀ hnorm
    have hz' : z ∈ ((B ⊔ B₀ : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hz
    rw [hset] at hz'
    obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_mul.mp hz'
    exact ⟨b, hb, c, hc, rfl⟩
  have K1 : ∀ Y : Subgroup G, B ≤ Y → Y < A ⊔ B → Y ≤ B₀ ⊔ B := by
    intro Y hBY hY
    have hYA : Y ⊓ A < A := by
      refine lt_of_le_of_ne inf_le_right fun h => ?_
      have hAY : A ≤ Y := inf_eq_right.mp h
      exact hY.ne (le_antisymm hY.le (sup_le hAY hBY))
    have hPY : A ⊓ B ≤ Y ⊓ A := fun x hx => ⟨hBY hx.2, hx.1⟩
    have hYB₀ : Y ⊓ A ≤ B₀ := hmax _ hPY hYA
    intro z hz
    obtain ⟨b, hb, a, ha, rfl⟩ := hsup z (hY.le hz)
    have haY : a ∈ Y := by
      have : b⁻¹ * (b * a) ∈ Y := Y.mul_mem (Y.inv_mem (hBY hb)) hz
      simpa using this
    have haB₀ : a ∈ B₀ := hYB₀ ⟨haY, ha⟩
    exact (B₀ ⊔ B).mul_mem (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left haB₀)
  have K2 : B₀ ⊔ B < A ⊔ B := by
    refine lt_of_le_of_ne (sup_le_sup_right hB₀A.le B) fun h => ?_
    have hAle : A ≤ B₀ ⊔ B := h ▸ le_sup_left
    apply hB₀A.ne
    refine le_antisymm hB₀A.le fun a ha => ?_
    obtain ⟨b, hb, c, hc, hbc⟩ := hsup0 a (hAle ha)
    have hcA : c ∈ A := hB₀A.le hc
    have hbA : b ∈ A := by
      have : a * c⁻¹ ∈ A := A.mul_mem ha (A.inv_mem hcA)
      rw [hbc] at this
      simpa using this
    have hbB₀ : b ∈ B₀ := hPB₀ ⟨hbA, hb⟩
    rw [hbc]
    exact B₀.mul_mem hbB₀ hc
  refine ⟨B₀ ⊔ B, isUniqueMaxOver_iff.mpr ⟨⟨K2, fun Z hZ1 hZ2 => ?_⟩, le_sup_right, fun N' hN' hBN' => ?_⟩⟩
  · by_contra hne
    have hZ : Z < A ⊔ B := lt_of_le_of_ne hZ2 hne
    exact absurd (K1 Z (le_sup_right.trans hZ1.le) hZ) (not_le_of_gt hZ1)
  · have hle : N' ≤ B₀ ⊔ B := K1 N' hBN' hN'.1
    by_contra hne
    have hlt : N' < B₀ ⊔ B := lt_of_le_of_ne hle hne
    exact K2.ne (hN'.2 _ hlt K2.le)


section Stage1

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement


end Stage1


section


end

end CFSG.ASVolI
