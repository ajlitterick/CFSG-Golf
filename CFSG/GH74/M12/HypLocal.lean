module

public import CFSG.GH74.M12.HypModel
public import CFSG.GH74.M12.HypAsc

public section

namespace CFSG.GH74.M12.Hyp

open Subgroup CFSG CFSG.GH74

@[expose] def tblSubgroup (L : List (List Nat)) (hone : tid ∈ L)
    (hmul : ∀ s ∈ L, ∀ t ∈ L, tmul s t ∈ L) (hinv : ∀ s ∈ L, tinv s ∈ L) : Subgroup ↥CJ where
  carrier := {x | tauC x ∈ L}
  mul_mem' := by
    intro a b ha hb
    show tauC (a * b) ∈ L
    rw [tauC_mul]
    exact hmul _ ha _ hb
  one_mem' := by
    show tauC 1 ∈ L
    rw [tauC_one]
    exact hone
  inv_mem' := by
    intro a ha
    show tauC a⁻¹ ∈ L
    rw [tauC_inv]
    exact hinv _ ha


theorem card_of_tauC
    {P : ↥CJ → Prop} (L : List (List Nat)) (hL : L.Nodup)
    (hsub : ∀ t ∈ L, t ∈ HT) (hP : ∀ x, P x ↔ tauC x ∈ L) :
    Nat.card {x // P x} = L.length := by
  have e : {x // P x} ≃ {t // t ∈ L} :=
    Equiv.ofBijective (fun x => ⟨tauC x.1, (hP x.1).1 x.2⟩)
      ⟨fun a b hab => Subtype.ext (tauC_injective (congrArg Subtype.val hab)), by
        rintro ⟨t, ht⟩
        obtain ⟨x, hx⟩ := tauC_real t (hsub t ht)
        refine ⟨⟨x, (hP x).2 (by rw [hx]; exact ht)⟩, Subtype.ext hx⟩⟩
  rw [Nat.card_congr e, card_mem_list L hL]

theorem card_CJ :
    Nat.card ↥CJ = 192 := by
  have := card_of_tauC (P := fun _ => True) HT HT_nodup (fun _ h => h)
    (fun x => by simp [tauC_mem x])
  rw [HT_length] at this
  rw [← this]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm

theorem card_tblSubgroup {L : List (List Nat)} {hone : tid ∈ L}
    {hmul : ∀ s ∈ L, ∀ t ∈ L, tmul s t ∈ L} {hinv : ∀ s ∈ L, tinv s ∈ L} (hL : L.Nodup)
    (hsub : ∀ t ∈ L, t ∈ HT) : Nat.card ↥(tblSubgroup L hone hmul hinv) = L.length :=
  card_of_tauC (P := fun x => x ∈ tblSubgroup L hone hmul hinv) L hL hsub (fun _ => Iff.rfl)

theorem normal_tblSubgroup
    {L : List (List Nat)} {hone : tid ∈ L}
    {hmul : ∀ s ∈ L, ∀ t ∈ L, tmul s t ∈ L} {hinv : ∀ s ∈ L, tinv s ∈ L}
    (hn : ∀ c ∈ HT, ∀ q ∈ L, tmul (tmul c q) (tinv c) ∈ L) :
    (tblSubgroup L hone hmul hinv).Normal where
  conj_mem n hn' g := by
    show tauC (g * n * g⁻¹) ∈ L
    rw [tauC_mul, tauC_mul, tauC_inv]
    exact hn _ (tauC_mem g) _ hn'

@[expose] def Qsub :
    Subgroup ↥CJ := tblSubgroup QT tid_mem_QT QT_mul QT_inv

@[expose] def Q1sub :
    Subgroup ↥CJ := tblSubgroup Q1T tid_mem_Q1T Q1T_mul Q1T_inv


theorem mem_Qsub {x : ↥CJ} : x ∈ Qsub ↔ tauC x ∈ QT := Iff.rfl


theorem QT_sub_HT : ∀ t ∈ QT, t ∈ HT := fun _ ht => (mem_QT_iff.1 ht).1

theorem card_Qsub : Nat.card ↥Qsub = 32 := by
  rw [Qsub, card_tblSubgroup QT_nodup QT_sub_HT, QT_length]


theorem Qsub_normal
    : Qsub.Normal := normal_tblSubgroup QT_normal

instance instNormalQsub :
    Qsub.Normal := Qsub_normal

theorem Q1sub_normal
    : Q1sub.Normal := normal_tblSubgroup Q1T_normal


theorem isPGroup_Qsub : IsPGroup 2 ↥Qsub :=
  IsPGroup.of_card (n := 5) (by rw [card_Qsub]; norm_num)

@[expose] def zJ : ↥CJ := ⟨Jelt, Jelt_mem_CJ⟩

theorem tauC_zJ : tauC zJ = JT := tbl_bfJ

theorem quotient_perm_three
    : Nonempty (↥CJ ⧸ Qsub ≃* Equiv.Perm (Fin 3)) := by
  have hcard : Nat.card (↥CJ ⧸ Qsub) = 6 := by
    have h := Subgroup.card_mul_index Qsub
    rw [card_Qsub, card_CJ] at h
    rw [← Subgroup.index_eq_card]
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := HQ_noncomm
  obtain ⟨cx, rfl⟩ := tauC_real c hc
  obtain ⟨dx, rfl⟩ := tauC_real d hd
  refine nonempty_mulEquiv_perm_three_of_card_six hcard (QuotientGroup.mk cx)
    (QuotientGroup.mk dx) ?_
  intro h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  apply hcd
  have h2 : tauC ((cx * dx)⁻¹ * (dx * cx)) ∈ QT := h
  rwa [tauC_mul, tauC_inv, tauC_mul, tauC_mul] at h2

theorem pCore_CJ :
    pCore 2 ↥CJ = Qsub := by
  apply le_antisymm
  · obtain ⟨e3⟩ := quotient_perm_three
    intro k hk
    have hK2 : IsPGroup 2 (pCore 2 ↥CJ) := pCore_isPGroup
    have h1 : ((pCore 2 ↥CJ).map (QuotientGroup.mk' Qsub)).Normal :=
      Subgroup.Normal.map (pCore_normal (G := ↥CJ) (p := 2)) (QuotientGroup.mk' Qsub)
        (QuotientGroup.mk'_surjective Qsub)
    have hN : (((pCore 2 ↥CJ).map (QuotientGroup.mk' Qsub)).map e3.toMonoidHom).Normal :=
      Subgroup.Normal.map h1 e3.toMonoidHom e3.surjective
    have hNp : IsPGroup 2 (((pCore 2 ↥CJ).map (QuotientGroup.mk' Qsub)).map e3.toMonoidHom) :=
      (hK2.map (QuotientGroup.mk' Qsub)).map e3.toMonoidHom
    have hbot := eq_bot_of_normal_isPGroup_perm_three
      (((pCore 2 ↥CJ).map (QuotientGroup.mk' Qsub)).map e3.toMonoidHom) hNp
    have hmem : e3 (QuotientGroup.mk' Qsub k) ∈
        ((pCore 2 ↥CJ).map (QuotientGroup.mk' Qsub)).map e3.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hk)
    rw [hbot] at hmem
    have h2 : e3 (QuotientGroup.mk' Qsub k) = 1 := by simpa using hmem
    have h3 : QuotientGroup.mk' Qsub k = 1 := e3.map_eq_one_iff.1 h2
    exact (QuotientGroup.eq_one_iff k).1 h3
  · exact le_sSup ⟨Qsub_normal, isPGroup_Qsub⟩

@[expose] def tauQ (x : ↥Qsub) : List Nat := tauC x.1

theorem tauQ_injective : Function.Injective tauQ := fun _ _ h =>
  Subtype.ext (tauC_injective h)

theorem tauQ_mem (x : ↥Qsub) : tauQ x ∈ QT := x.2

theorem tauQ_mul
    (x y : ↥Qsub) : tauQ (x * y) = tmul (tauQ x) (tauQ y) := tauC_mul x.1 y.1

theorem tauQ_inv
    (x : ↥Qsub) : tauQ x⁻¹ = tinv (tauQ x) := tauC_inv x.1

theorem tauQ_real : ∀ t ∈ QT, ∃ x : ↥Qsub, tauQ x = t := by
  intro t ht
  obtain ⟨x, hx⟩ := tauC_real t (QT_sub_HT t ht)
  exact ⟨⟨x, by rw [mem_Qsub, hx]; exact ht⟩, hx⟩

theorem tid_ne_JT : tid ≠ JT := by decide +kernel

theorem mem_center_Qsub
    {x : ↥Qsub} : x ∈ center ↥Qsub ↔ tauQ x = tid ∨ tauQ x = JT := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    refine (QT_center _ (tauQ_mem x)).1 ?_
    intro t ht
    obtain ⟨y, rfl⟩ := tauQ_real t ht
    rw [← tauQ_mul, ← tauQ_mul, h y]
  · intro h y
    apply tauQ_injective
    rw [tauQ_mul, tauQ_mul]
    exact ((QT_center _ (tauQ_mem x)).2 h _ (tauQ_mem y)).symm

theorem card_center_Qsub : Nat.card ↥(center ↥Qsub) = 2 := by
  have e : ↥(center ↥Qsub) ≃ {t // t ∈ [tid, JT]} :=
    Equiv.ofBijective (fun c => ⟨tauQ c.1, by
        have := mem_center_Qsub.1 c.2
        simpa using this⟩)
      ⟨fun a b hab => Subtype.ext (tauQ_injective (congrArg Subtype.val hab)), by
        rintro ⟨t, ht⟩
        have ht' : t = tid ∨ t = JT := by simpa using ht
        rcases ht' with rfl | rfl
        · exact ⟨⟨1, Subgroup.one_mem _⟩, Subtype.ext (tauC_one)⟩
        · obtain ⟨y, hy⟩ := tauQ_real JT JT_mem_QT
          exact ⟨⟨y, mem_center_Qsub.2 (Or.inr hy)⟩, Subtype.ext hy⟩⟩
  rw [Nat.card_congr e, card_mem_list [tid, JT] (by simp [tid_ne_JT])]
  rfl

theorem isElementaryAbelian_Qsub :
    IsElementaryAbelian 2 (↥Qsub ⧸ center ↥Qsub) := by
  have hcomm : ∀ a b : ↥Qsub ⧸ center ↥Qsub, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_center_Qsub]
    rw [tauQ_mul, tauQ_inv, tauQ_mul, tauQ_mul]
    exact QT_comm _ (tauQ_mem x) _ (tauQ_mem y)
  have hexp : Monoid.exponent (↥Qsub ⧸ center ↥Qsub) ∣ 2 := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    induction a using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_Qsub, pow_two, tauQ_mul]
    exact QT_sq _ (tauQ_mem x)
  exact { toIsMulCommutative := ⟨⟨hcomm⟩⟩, exponent_dvd_p := hexp }

theorem nontrivial_quotient_Qsub :
    Nontrivial (↥Qsub ⧸ center ↥Qsub) := by
  obtain ⟨s, hs, hs1, hs2⟩ := QT_noncentral
  obtain ⟨x, rfl⟩ := tauQ_real s hs
  refine ⟨⟨QuotientGroup.mk x, 1, ?_⟩⟩
  intro h
  rw [QuotientGroup.eq_one_iff, mem_center_Qsub] at h
  rcases h with h | h
  · exact hs1 h
  · exact hs2 h

theorem isExtraspecial_Qsub : IsExtraspecial 2 ↥Qsub where
  center_order_p := card_center_Qsub
  quotient_elementary_abelian := isElementaryAbelian_Qsub
  quotient_nontrivial := nontrivial_quotient_Qsub

theorem localHyp_CJ :
    LocalHyp ↥CJ zJ where
  card_eq := card_CJ
  card_core := by rw [pCore_CJ]; exact card_Qsub
  extraspecial := by rw [pCore_CJ]; exact isExtraspecial_Qsub
  quotient_S3 := by
    obtain ⟨e3⟩ := quotient_perm_three
    exact ⟨(QuotientGroup.quotientMulEquivOfEq pCore_CJ).trans e3⟩
  centralizer_X := by
    intro x hx q hq hcomm
    rw [pCore_CJ] at hq
    have hx3 : x * (x * x) = 1 := by
      have h3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      rw [← pow_three]; exact h3
    have hx1 : x ≠ 1 := by
      intro h; rw [h, orderOf_one] at hx; omega
    have h1 : tmul (tauC x) (tmul (tauC x) (tauC x)) = tid := by
      rw [← tauC_mul, ← tauC_mul, hx3, tauC_one]
    have h2 : tauC x ≠ tid := by
      intro h
      apply hx1
      apply tauC_injective
      rw [h, tauC_one]
    have h3 : tmul (tauC q) (tauC x) = tmul (tauC x) (tauC q) := by
      rw [← tauC_mul, ← tauC_mul, hcomm.symm]
    rcases QT_order3 (tauC x) (tauC_mem x) h1 h2 (tauC q) hq h3 with h | h
    · have : q = 1 := tauC_injective (by rw [h, tauC_one])
      rw [this]; exact Subgroup.one_mem _
    · have : q = zJ := tauC_injective (by rw [h, tauC_zJ])
      rw [this]; exact Subgroup.mem_zpowers _

@[expose] def q8T (x y : List Nat) : QuaternionGroup 2 → List Nat
  | .a i => tpow x i.val
  | .xa i => tmul (tpow x ((4 - i.val) % 4)) y

theorem q8T_one : q8T x1T y1T 1 = tid := by decide +kernel

theorem q8T_mul : ∀ g h : QuaternionGroup 2,
    tmul (q8T x1T y1T g) (q8T x1T y1T h) = q8T x1T y1T (g * h) := by decide +kernel

theorem q8T_injective : ∀ g h : QuaternionGroup 2,
    q8T x1T y1T g = q8T x1T y1T h → g = h := by decide +kernel

theorem q8T_mem : ∀ g : QuaternionGroup 2, q8T x1T y1T g ∈ Q1T := by decide +kernel

theorem q8T_surj : ∀ t ∈ Q1T, ∃ g : QuaternionGroup 2, q8T x1T y1T g = t := by decide +kernel


theorem q8T_mem_HT (g : QuaternionGroup 2) : q8T x1T y1T g ∈ HT :=
  QT_sub_HT _ (Q1T_sub _ (q8T_mem g))

noncomputable def q8Hom : QuaternionGroup 2 →* ↥CJ where
  toFun g := Classical.choose (tauC_real (q8T x1T y1T g) (q8T_mem_HT g))
  map_one' := by
    apply tauC_injective
    rw [Classical.choose_spec (tauC_real (q8T x1T y1T 1) (q8T_mem_HT 1)), q8T_one, tauC_one]
  map_mul' g h := by
    apply tauC_injective
    rw [tauC_mul, Classical.choose_spec (tauC_real (q8T x1T y1T g) (q8T_mem_HT g)),
      Classical.choose_spec (tauC_real (q8T x1T y1T h) (q8T_mem_HT h)),
      Classical.choose_spec (tauC_real (q8T x1T y1T (g * h)) (q8T_mem_HT (g * h))), q8T_mul]

theorem tauC_q8Hom
    (g : QuaternionGroup 2) : tauC (q8Hom g) = q8T x1T y1T g :=
  Classical.choose_spec (tauC_real (q8T x1T y1T g) (q8T_mem_HT g))

theorem q8Hom_injective : Function.Injective q8Hom := by
  intro g h hgh
  apply q8T_injective
  rw [← tauC_q8Hom, ← tauC_q8Hom, hgh]

theorem q8Hom_range : q8Hom.range = Q1sub := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    show tauC (q8Hom g) ∈ Q1T
    rw [tauC_q8Hom]
    exact q8T_mem g
  · intro hx
    obtain ⟨g, hg⟩ := q8T_surj (tauC x) hx
    exact ⟨g, tauC_injective (by rw [tauC_q8Hom, hg])⟩

theorem Q1sub_mulEquiv : Nonempty (↥Q1sub ≃* QuaternionGroup 2) :=
  ⟨(MulEquiv.subgroupCongr q8Hom_range.symm).trans (MonoidHom.ofInjective q8Hom_injective).symm⟩

theorem exists_q8_normal_CJ
    : ∃ K ∈ q8Subgroups (pCore 2 ↥CJ), K.Normal := by
  refine ⟨Q1sub, ⟨?_, Q1sub_mulEquiv⟩, Q1sub_normal⟩
  rw [pCore_CJ]
  intro x hx
  exact (mem_Qsub).2 (Q1T_sub _ hx)


end CFSG.GH74.M12.Hyp
