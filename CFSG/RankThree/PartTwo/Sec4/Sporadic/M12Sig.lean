module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12SigCheck
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport
public import CFSG.RankThree.PartTwo.Toolkit.M12Facts
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import Certificates.Certificate5950
public import CFSG.Certificates.Kernel.M12SigCoset

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig

open CFSG CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 Subgroup CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.RankThree.Asc83Table
open scoped commutatorElement


theorem exists_mem_of_mem_nf2T (B : E9Basis G12) {uT vT s : List ℕ} (hu : tbl B.a.1 = uT)
    (hv : tbl B.b.1 = vT) (hs : s ∈ nf2T uT vT) : ∃ e ∈ B.sub, tbl e.1 = s := by
  obtain ⟨i, -, j, -, rfl⟩ := mem_nf2T.mp hs
  refine ⟨B.a ^ i * B.b ^ j, B.sub.mul_mem (B.sub.pow_mem (subset_closure (by simp)) _)
    (B.sub.pow_mem (subset_closure (by simp)) _), ?_⟩
  rw [tblG_mul, tblG_pow, tblG_pow, hu, hv]


theorem exists_mem_A {s : List ℕ} (hs : s ∈ AT) : ∃ e ∈ basisA.sub, tbl e.1 = s :=
  exists_mem_of_mem_nf2T basisA tbl_z tbl_a hs


theorem invariant_E : invariantPiSubgroups ⊤ basisE.sub (piOf 2) = {⊥} :=
  sig_invariant_E

theorem invariant_F : invariantPiSubgroups ⊤ basisF.sub (piOf 2) = {⊥} :=
  sig_invariant_F

theorem gam_facts : (∀ p ∈ gamA ++ gamB, predP (if p.1 then zT else aT) (prodT p.2) = true) ∧
    gamProd gamA = tA ∧ gamProd gamB = tB := by
  have h := sig_small.2.2.1
  simp only [chkGamma, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

@[expose] def elt (k : Idx) : G12 := ⟨prodP k, prodP_mem k⟩

theorem tbl_elt (k : Idx) : tbl (elt k).1 = prodT k := tbl_prodP k

theorem tbl_prod_elt (L : List (Bool × Idx)) :
    tbl ((L.map fun p => elt p.2).prod).1 = gamProd L := by
  induction L with
  | nil => exact tblG_one
  | cons p L ih => rw [List.map_cons, List.prod_cons, tblG_mul, ih, tbl_elt]; rfl

theorem z_mem_A : ⁅x, y⁆ ∈ basisA.sub := subset_closure (Or.inl rfl)

theorem z_cube : ⁅x, y⁆ ^ 3 = 1 := cube_of_mem_P0 z_mem_P0

theorem zpowers_le_gamma {u : G12} (hu : u ∈ basisA.sub) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) :
    normalizer ((zpowers u : Subgroup G12) : Set G12) ≤ gamma 1 basisA.sub := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine normalizer_le_gamma (zpowers_le.mpr hu) ?_
  rw [CFSG.RankThree.PartTwo.Late.one_le_pRank_three_iff]
  · intro h
    exact hu1 (by simpa using (zpowers_eq_bot.mp h))
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1, pow_one]

theorem elt_mem_gamma {p : Bool × Idx} (hp : p ∈ gamA ++ gamB) :
    elt p.2 ∈ gamma 1 basisA.sub := by
  have h := gam_facts.1 p hp
  cases hb : p.1
  · rw [hb] at h
    refine zpowers_le_gamma a_mem_A a_cube a_ne_one ?_
    rw [mem_normalizer_zpowers_iff tbl_a a_cube a_ne_one, tbl_elt]
    simpa [predP] using h
  · rw [hb] at h
    refine zpowers_le_gamma z_mem_A z_cube z_ne_one ?_
    rw [mem_normalizer_zpowers_iff tbl_z z_cube z_ne_one, tbl_elt]
    simpa [predP] using h

theorem prod_mem_gamma {L : List (Bool × Idx)} (hL : ∀ p ∈ L, p ∈ gamA ++ gamB) :
    (L.map fun p => elt p.2).prod ∈ gamma 1 basisA.sub := by
  refine list_prod_mem fun g hg => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  exact elt_mem_gamma (hL p hp)

theorem gamma_A : gamma 1 basisA.sub = ⊤ := by
  have ha : CFSG.Sporadic.Mathieu.m12a = (gamA.map fun p => elt p.2).prod := by
    rw [eq_iff_tbl, tbl_prod_elt, gam_facts.2.1, ← tbl_m12gA]
  have hb : CFSG.Sporadic.Mathieu.m12b = (gamB.map fun p => elt p.2).prod := by
    rw [eq_iff_tbl, tbl_prod_elt, gam_facts.2.2, ← tbl_m12gB]
  rw [eq_top_iff, ← m12_closure_eq_top, closure_le]
  rintro g (rfl | rfl)
  · rw [ha]
    exact prod_mem_gamma fun p hp => List.mem_append_left _ hp
  · rw [hb]
    exact prod_mem_gamma fun p hp => List.mem_append_right _ hp

theorem mem_fin3 (i : Fin 3) : i.val ∈ List.range 3 := List.mem_range.mpr i.isLt

theorem vstruct (i : Fin 3) :
    tid ∈ VT i ∧ (∀ s ∈ VT i, ∀ t ∈ VT i, tmul s t ∈ VT i) ∧ (∀ s ∈ VT i, tinv s ∈ VT i) ∧
    (VT i).Nodup ∧ (VT i).length = 4 ∧ (∀ s ∈ VT i, commT (aiT i) s = true) ∧
    (∀ f ∈ AT, ∀ v ∈ VT i, tconj f v ∈ VT i) ∧
    (∀ u ∈ VT i, u ≠ tid → (∃ f ∈ AT, tconj f u = vg1 i) ∧ ∃ f ∈ AT, tconj f u = vg2 i) ∧
    (∀ j ∈ List.range 3, j ≠ i.val → vg1 i ∉ VT j) ∧
    (∀ s ∈ P0T, ∃ w ∈ List.range 3, ∀ v ∈ VT i, tconj (tinv s) v ∈ VT w) ∧
    (∀ w ∈ List.range 3, ∃ s ∈ P0T, ∀ v ∈ VT i, tconj (tinv s) v ∈ VT w) := by
  have h := List.all_eq_true.mp sig_small.2.1 i.val (mem_fin3 i)
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.contains_iff_mem,
    decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun u hu hne => (h8 u hu).resolve_left hne, ?_, h10, h11⟩
  intro j hj hji hmem
  rcases h9 j hj with h | h
  · exact hji h
  · rw [Bool.eq_false_iff] at h
    exact h (List.contains_iff_mem.mpr hmem)

theorem vg1_mem (i : Fin 3) : vg1 i ∈ VT i := by
  rw [vg1, List.getD_eq_getElem _ _ (by rw [(vstruct i).2.2.2.2.1]; norm_num)]
  exact List.getElem_mem _

@[expose] def V (i : Fin 3) : Subgroup G12 where
  carrier := {g | tbl g.1 ∈ VT i}
  mul_mem' {g h} hg hh := by
    change tbl (g * h).1 ∈ VT i
    rw [tblG_mul]
    exact (vstruct i).2.1 _ hg _ hh
  one_mem' := by
    change tbl (1 : G12).1 ∈ VT i
    rw [tblG_one]
    exact (vstruct i).1
  inv_mem' {g} hg := by
    change tbl g⁻¹.1 ∈ VT i
    rw [tblG_inv]
    exact (vstruct i).2.2.1 _ hg

theorem mem_V {i : Fin 3} {g : G12} : g ∈ V i ↔ tbl g.1 ∈ VT i := Iff.rfl

theorem exists_of_mem_VT {i : Fin 3} {t : List ℕ} (ht : t ∈ VT i) : ∃ g : G12, tbl g.1 = t := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp ht
  exact ⟨elt k, tbl_elt k⟩

theorem card_V (i : Fin 3) : Nat.card (V i) = 4 := by
  classical
  let e : V i → {t // t ∈ VT i} := fun g => ⟨tbl g.1.1, g.2⟩
  have hinj : Function.Injective e := fun g h hgh =>
    Subtype.ext (eq_iff_tbl.mpr (congrArg Subtype.val hgh))
  have hsurj : Function.Surjective e := by
    rintro ⟨t, ht⟩
    obtain ⟨g, hg⟩ := exists_of_mem_VT ht
    exact ⟨⟨g, by rw [mem_V, hg]; exact ht⟩, Subtype.ext hg⟩
  rw [Nat.card_congr (Equiv.ofBijective e ⟨hinj, hsurj⟩), card_mem_list _ (vstruct i).2.2.2.1,
    (vstruct i).2.2.2.2.1]

theorem isPGroup_V (i : Fin 3) : IsPGroup 2 (V i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 2) (by rw [card_V]; norm_num)

theorem V_ne (i j : Fin 3) (h : V i = V j) : i = j := by
  by_contra hij
  obtain ⟨g, hg⟩ := exists_of_mem_VT (vg1_mem i)
  have hgi : g ∈ V i := by rw [mem_V, hg]; exact vg1_mem i
  rw [h, mem_V, hg] at hgi
  exact (vstruct i).2.2.2.2.2.2.2.2.1 j.val (mem_fin3 j) (fun h' => hij (Fin.ext h'.symm)) hgi

theorem A_le_normalizer_V (i : Fin 3) :
    basisA.sub ≤ normalizer ((V i : Subgroup G12) : Set G12) := by
  have key : ∀ f ∈ basisA.sub, ∀ v ∈ V i, f * v * f⁻¹ ∈ V i := by
    intro f hf v hv
    rw [mem_V, tblG_conj]
    exact (vstruct i).2.2.2.2.2.2.1 _ ((mem_A_iff f).mp hf) _ hv
  intro f hf
  rw [mem_normalizer_iff]
  intro v
  refine ⟨key f hf v, fun hv => ?_⟩
  have := key f⁻¹ (inv_mem hf) _ hv
  simpa [mul_assoc] using this

@[expose] def ai (i : Fin 3) : G12 := ⁅x, y⁆ ^ i.val * (x * y)

theorem tbl_ai (i : Fin 3) : tbl (ai i).1 = aiT i := by
  rw [ai, tblG_mul, tblG_pow, tbl_z, tbl_a]
  rfl

theorem mem_centralizer_ai_iff (i : Fin 3) (g : G12) :
    g ∈ centralizer ({ai i} : Set G12) ↔ predC [aiT i] (tbl g.1) = true := by
  rw [mem_centralizer_singleton_iff, predC, List.all_cons, List.all_nil, Bool.and_true,
    beq_iff_eq, ← tbl_ai, ← tblG_mul, ← tblG_mul]
  exact eq_iff_tbl

theorem exists_idxC {i : Fin 3} {g : G12}
    (hg : g ∈ centralizer ({ai i} : Set G12)) : ∃ k ∈ idxC i, tbl g.1 = prodT k := by
  have h := mem_centralizer_singleton_iff.mp hg
  refine sig_mem_C i.isLt ?_
  first
  | exact h
  | exact h.symm

theorem card_C (i : Fin 3) :
    Nat.card (centralizer ({ai i} : Set G12)) = 36 := by
  classical
  have hL := List.all_eq_true.mp sig_small.2.2.2 i.val (mem_fin3 i)
  rw [Bool.and_eq_true, decide_eq_true_eq] at hL
  have hlen : ((idxC i).map prodT).length = 36 := by
    rw [List.length_map]
    fin_cases i <;> rfl
  rw [← hlen, ← card_mem_list _ hL.2]
  let e : centralizer ({ai i} : Set G12) → {t // t ∈ (idxC i).map prodT} := fun g =>
    ⟨tbl g.1.1, by
      obtain ⟨k, hk, he⟩ := exists_idxC g.2
      exact List.mem_map.mpr ⟨k, hk, he.symm⟩⟩
  have hinj : Function.Injective e := fun g h hgh =>
    Subtype.ext (eq_iff_tbl.mpr (congrArg Subtype.val hgh))
  have hsurj : Function.Surjective e := by
    rintro ⟨t, ht⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
    refine ⟨⟨elt k, (mem_centralizer_ai_iff i _).mpr ?_⟩, Subtype.ext (tbl_elt k)⟩
    rw [tbl_elt]
    exact List.all_eq_true.mp hL.1 k hk
  exact (Nat.card_congr (Equiv.ofBijective e ⟨hinj, hsurj⟩))

theorem V_le_C (i : Fin 3) : V i ≤ centralizer ({ai i} : Set G12) := by
  intro v hv
  rw [mem_centralizer_singleton_iff, eq_iff_tbl, tblG_mul, tblG_mul, tbl_ai]
  have := (vstruct i).2.2.2.2.2.1 _ hv
  rw [commT, beq_iff_eq] at this
  exact this

theorem normal_V (i : Fin 3) :
    ((V i).subgroupOf (centralizer ({ai i} : Set G12))).Normal := by
  constructor
  intro v hv c
  rw [mem_subgroupOf] at hv ⊢
  change (c : G12) * v * (c : G12)⁻¹ ∈ V i
  obtain ⟨k, hk, hck⟩ := exists_idxC c.2
  have h := sig_small.1
  simp only [chkNormal, List.all_eq_true, List.contains_iff_mem] at h
  rw [mem_V, tblG_conj, hck]
  exact h i.val (mem_fin3 i) k hk _ hv

theorem pCore_centralizer
    (i : Fin 3) :
    inSubgroup (CFSG.pCore 2) (centralizer ({ai i} : Set G12)) = V i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({ai i} : Set G12)
  have hp : IsPGroup 2 ((V i).subgroupOf C) := (isPGroup_V i).comap_of_injective _ (by
    intro a b h; exact Subtype.ext (by simpa using congrArg Subtype.val h))
  have hle : (V i).subgroupOf C ≤ CFSG.pCore 2 C := le_sSup ⟨normal_V i, hp⟩
  have h1 : V i ≤ inSubgroup (CFSG.pCore 2) C := by
    intro v hv
    exact ⟨⟨v, V_le_C i hv⟩, hle (by rw [mem_subgroupOf]; exact hv), rfl⟩
  refine (Subgroup.eq_of_le_of_card_ge h1 ?_).symm
  rw [card_V, inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := C)).exists_card_eq
  have hdvd : 2 ^ n ∣ 36 := hn ▸ card_C i ▸ Subgroup.card_subgroup_dvd_card _
  have hn2 : n ≤ 2 := by
    by_contra hc
    have : 2 ^ 3 ∣ 36 := (pow_dvd_pow 2 (by omega)).trans hdvd
    omega
  rw [hn]
  exact pow_le_pow_right₀ (by norm_num) hn2


theorem le_V_of_mem_invariant {Y : Subgroup G12}
    (hY : Y ∈ invariantPiSubgroups ⊤ basisA.sub (piOf 2)) (hne : Y ≠ ⊥) :
    ∃ i : Fin 3, Y ≤ V i := by
  obtain ⟨i, hi, h⟩ := sig_le_V hY hne
  exact ⟨⟨i, hi⟩, fun y hy => mem_V.mpr (h y hy)⟩


@[expose] def wL (l : Int) : G12 := ⟨letterP l, letterP_mem l⟩


theorem tbl_f (i j : ℕ) : tbl (⁅x, y⁆ ^ i * (x * y) ^ j).1 = tmul (tpow zT i) (tpow aT j) := by
  rw [tblG_mul, tblG_pow, tblG_pow, tbl_z, tbl_a]

theorem f_mem_A (i j : ℕ) : ⁅x, y⁆ ^ i * (x * y) ^ j ∈ basisA.sub :=
  basisA.sub.mul_mem (basisA.sub.pow_mem z_mem_A _) (basisA.sub.pow_mem a_mem_A _)


theorem le_inner_of_mem_invariant
    {X : Subgroup (MulAut G12)}
    (hX : X ∈ invariantPiSubgroups ⊤ (basisA.sub.map (MulAut.conj : G12 →* MulAut G12))
      (piOf 2)) : X ≤ (MulAut.conj : G12 →* MulAut G12).range := by
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 basisA.sub := IsPGroup.of_card (n := 2) (by rw [basisA.card]; norm_num)
  have hidx : (MulAut.conj : G12 →* MulAut G12).range.index = 2 := by
    have hcard : Nat.card (MulAut.conj : G12 →* MulAut G12).range = 95040 := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective conj_injective,
        Subgroup.card_top, CFSG.Sporadic.Mathieu.card_M12]
    have h := Subgroup.card_mul_index (MulAut.conj : G12 →* MulAut G12).range
    rw [hcard, card_mulAut] at h
    omega
  exact CFSG.KC.M12Sig.le_range_conj_of_fixed conj_injective hidx (by norm_num) hA3 sig_inner
    hX.2.1 hX.2.2

noncomputable abbrev V' (i : Fin 3) : Subgroup (MulAut G12) :=
  (V i).map (MulAut.conj : G12 →* MulAut G12)

theorem V'_mem (i : Fin 3) :
    V' i ∈ invariantPiSubgroups ⊤ (basisA.sub.map (MulAut.conj : G12 →* MulAut G12)) (piOf 2) := by
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
  refine ⟨le_top, (isPGroup_V i).map _, ?_⟩
  exact (Subgroup.map_mono (A_le_normalizer_V i)).trans (Subgroup.le_normalizer_map _)

theorem le_V'_of_mem
    {X : Subgroup (MulAut G12)}
    (hX : X ∈ invariantPiSubgroups ⊤ (basisA.sub.map (MulAut.conj : G12 →* MulAut G12))
      (piOf 2)) : ∃ i : Fin 3, X ≤ V' i := by
  have hle := le_inner_of_mem_invariant hX
  set Y := X.comap (MulAut.conj : G12 →* MulAut G12)
  have hXY : X = Y.map (MulAut.conj : G12 →* MulAut G12) := (Subgroup.map_comap_eq_self hle).symm
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hX
  have hYinv : Y ∈ invariantPiSubgroups ⊤ basisA.sub (piOf 2) := by
    rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
    refine ⟨le_top, hX.2.1.comap_of_injective _ conj_injective, fun f hf => ?_⟩
    rw [mem_normalizer_iff]
    intro w
    have hcf := hX.2.2 (mem_map_of_mem (MulAut.conj : G12 →* MulAut G12) hf)
    rw [mem_normalizer_iff] at hcf
    rw [mem_comap, mem_comap, hcf (MulAut.conj w), map_mul, map_mul, map_inv]
  by_cases hYb : Y = ⊥
  · exact ⟨0, by rw [hXY, hYb, Subgroup.map_bot]; exact bot_le⟩
  · obtain ⟨i, hi⟩ := le_V_of_mem_invariant hYinv hYb
    exact ⟨i, by rw [hXY]; exact Subgroup.map_mono hi⟩

theorem maxInvariant_A :
    maxInvariantPiSubgroups ⊤ (basisA.sub.map (MulAut.conj : G12 →* MulAut G12)) (piOf 2) =
      {X | ∃ i : Fin 3, X = V' i} := by
  ext X
  rw [mem_maxInvariantPiSubgroups_iff]
  constructor
  · rintro ⟨hX, hmax⟩
    obtain ⟨i, hi⟩ := le_V'_of_mem hX
    exact ⟨i, (hmax _ (V'_mem i) hi).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨V'_mem i, fun Y hY hle => ?_⟩
    obtain ⟨j, hj⟩ := le_V'_of_mem hY
    have hij : V i ≤ V j := (Subgroup.map_le_map_iff_of_injective conj_injective).mp (hle.trans hj)
    have heq : V i = V j :=
      Subgroup.eq_of_le_of_card_ge hij (by rw [card_V, card_V])
    obtain rfl := V_ne i j heq
    exact le_antisymm hj hle

theorem centralizer_singleton_inv (a : G12) :
    centralizer ({a⁻¹} : Set G12) = centralizer ({a} : Set G12) := by
  ext g
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

theorem exists_pCore_eq
    {a : G12} (ha : a ∈ basisA.sub)
    (hZ : a ∉ P0 ⊓ centralizer (P0 : Set G12)) :
    ∃ i : Fin 3, inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G12)) = V i := by
  rw [inf_centralizer_eq_map_center, center_P0] at hZ
  obtain ⟨i, j, hi, hj, rfl⟩ := basisA.exists_pow_mul_pow ha
  have hAa : basisA.a = ⁅x, y⁆ := rfl
  rw [hAa, basisA_b] at hZ ⊢
  interval_cases j
  · exfalso
    apply hZ
    rw [pow_zero, mul_one]
    exact (zpowers _).pow_mem (mem_zpowers _) i
  · refine ⟨⟨i, hi⟩, ?_⟩
    rw [pow_one]
    exact pCore_centralizer ⟨i, hi⟩
  · have key : ∀ i' (hi' : i' < 3), tinv (tmul (tpow zT i) (tpow aT 2)) =
        tmul (tpow zT i') (tpow aT 1) →
        inSubgroup (CFSG.pCore 2) (centralizer ({⁅x, y⁆ ^ i * (x * y) ^ 2} : Set G12)) =
          V ⟨i', hi'⟩ := by
      intro i' hi' h'
      have hai : (⁅x, y⁆ ^ i * (x * y) ^ 2)⁻¹ = ai ⟨i', hi'⟩ := by
        rw [eq_iff_tbl, tblG_inv, tbl_f, h', tbl_ai]
        rfl
      rw [← centralizer_singleton_inv, hai]
      exact pCore_centralizer ⟨i', hi'⟩
    obtain ⟨-, -, h0, h1, h2⟩ := conj_tables
    interval_cases i
    · exact ⟨_, key 0 (by norm_num) h0⟩
    · exact ⟨_, key 2 (by norm_num) h1⟩
    · exact ⟨_, key 1 (by norm_num) h2⟩

theorem exists_mem_P0 {s : List ℕ} (hs : s ∈ P0T) : ∃ g ∈ P0, tbl g.1 = s := by
  obtain ⟨i, -, j, -, k, -, rfl⟩ := mem_nf3T.mp hs
  have ht : tbl (x ^ i * y ^ j * ⁅x, y⁆ ^ k).1 =
      tmul (tmul (tpow xT i) (tpow yT j)) (tpow zT k) := by
    rw [tblG_mul, tblG_mul, tblG_pow, tblG_pow, tblG_pow, tbl_x, tbl_y, tbl_z]
  refine ⟨_, (mem_P0_iff _).mpr ?_, ht⟩
  rw [ht]
  exact hs

theorem conjugate_V_le {i w : Fin 3} {g : G12}
    (h : ∀ v ∈ VT i, tconj (tinv (tbl g.1)) v ∈ VT w) : conjugate (V i) g = V w := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨v, hv, rfl⟩
    change g⁻¹ * v * g⁻¹⁻¹ ∈ V w
    rw [mem_V, tblG_conj, tblG_inv]
    exact h _ hv
  · rw [card_V, conjugate, Subgroup.card_map_of_injective (MulAut.conj _).injective, card_V]

theorem image_conjugate_pCore
    {a : G12} (ha : a ∈ basisA.sub)
    (hZ : a ∉ P0 ⊓ centralizer (P0 : Set G12)) :
    (fun g : G12 => (conjugate (inSubgroup (CFSG.pCore 2) (centralizer {a})) g).map
        (MulAut.conj : G12 →* MulAut G12)) '' (P0 : Set G12) = {X | ∃ i : Fin 3, X = V' i} := by
  obtain ⟨i, hi⟩ := exists_pCore_eq ha hZ
  rw [hi]
  ext X
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨w, hw, hwv⟩ := (vstruct i).2.2.2.2.2.2.2.2.2.1 _ ((mem_P0_iff g).mp hg)
    refine ⟨⟨w, List.mem_range.mp hw⟩, ?_⟩
    dsimp only
    rw [conjugate_V_le (w := ⟨w, List.mem_range.mp hw⟩) hwv]
  · rintro ⟨w, rfl⟩
    obtain ⟨s, hs, hsv⟩ := (vstruct i).2.2.2.2.2.2.2.2.2.2 w.val (mem_fin3 w)
    obtain ⟨g, hg, rfl⟩ := exists_mem_P0 hs
    refine ⟨g, hg, ?_⟩
    dsimp only
    rw [conjugate_V_le hsv]

end CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
