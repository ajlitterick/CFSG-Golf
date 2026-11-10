module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicWeyl
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherRoots
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherInvariant

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (rootVec rootVec_eq_rootVec_iff
  simpleSnd inl_ne_simpleSnd simpleRootVec rootVec_simpleSnd simpleRefl simpleRefl_mem
  simpleRefl_mul_self)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem hypGram_mul_single (a b : HypIndex r ε) (c : K) :
    hypGram r ε K * single a b c = single (hypPartner a) b c := by
  ext x y
  rw [hypGram_mul_apply, single_apply, single_apply]
  have hiff : (a = hypPartner x) ↔ (hypPartner a = x) := by
    constructor <;> rintro rfl <;> simp
  simp only [hiff]

theorem single_mul_hypGram (a b : HypIndex r ε) (c : K) :
    single a b c * hypGram r ε K = single a (hypPartner b) c := by
  ext x y
  rw [mul_hypGram_apply, single_apply, single_apply]
  have hiff : (b = hypPartner y) ↔ (hypPartner b = y) := by
    constructor <;> rintro rfl <;> simp
  simp only [hiff]

theorem conjTranspose_single (h : UnitaryFieldData p f K) (a b : HypIndex r ε) (c : K) :
    ((single a b c).map h.bar)ᵀ = single b a (h.bar c) := by
  rw [map_single _ _ _ h.bar, transpose_single]

theorem lineCoord_injective : Function.Injective (lineCoord (r := r) (ε := ε)) := by
  intro x y hxy
  rcases x with x | x <;> rcases y with y | y <;> simp_all [lineCoord]


theorem lineCoord_swap_ne (x : Fin r ⊕ Fin r) : lineCoord (ε := ε) x.swap ≠ lineCoord x :=
  fun h => SymplecticHigher.swap_ne_self x (lineCoord_injective h)

@[expose] noncomputable def uRootDom (h : UnitaryFieldData p f K) (a b : Fin r ⊕ Fin r) :
    AddSubgroup K :=
  if b = a.swap then h.traceZero else ⊤

theorem uRootDom_of_ne (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r} (hb : b ≠ a.swap) :
    uRootDom h a b = ⊤ := by
  simp [uRootDom, hb]

theorem uRootDom_swap (h : UnitaryFieldData p f K) (a : Fin r ⊕ Fin r) :
    uRootDom h a a.swap = h.traceZero := by
  simp [uRootDom]

variable (ε) in
@[expose] noncomputable def uRootNil (h : UnitaryFieldData p f K) (a b : Fin r ⊕ Fin r) (t : K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K :=
  if b = a.swap then single (lineCoord a) (lineCoord b) t
  else single (lineCoord a) (lineCoord b) t - single (lineCoord b.swap) (lineCoord a.swap) (h.bar t)

variable (ε) in
@[expose] noncomputable def uRootMat (h : UnitaryFieldData p f K) (a b : Fin r ⊕ Fin r) (t : K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K :=
  1 + uRootNil ε h a b t

theorem uRootNil_add (h : UnitaryFieldData p f K) (a b : Fin r ⊕ Fin r) (s t : K) :
    uRootNil ε h a b (s + t) = uRootNil ε h a b s + uRootNil ε h a b t := by
  unfold uRootNil
  split_ifs
  · rw [single_add]
  · rw [single_add, map_add, single_add]
    abel

theorem uRootNil_zero (h : UnitaryFieldData p f K) (a b : Fin r ⊕ Fin r) :
    uRootNil ε h a b 0 = 0 := by
  unfold uRootNil
  split_ifs <;> simp

theorem uRootNil_mul {h : UnitaryFieldData p f K} {a b : Fin r ⊕ Fin r} (hab : a ≠ b)
    (s t : K) : uRootNil ε h a b s * uRootNil ε h a b t = 0 := by
  have hab' : lineCoord (ε := ε) a ≠ lineCoord b := fun h' => hab (lineCoord_injective h')
  have hsw : lineCoord (ε := ε) a.swap ≠ lineCoord b.swap := fun h' =>
    hab (SymplecticHigher.swap_injective' (lineCoord_injective h'))
  unfold uRootNil
  split_ifs with hb
  · rw [single_mul_single_of_ne _ _ _ _ (Ne.symm hab')]
  · simp only [Matrix.sub_mul, Matrix.mul_sub,
      single_mul_single_of_ne _ _ _ _ (Ne.symm hab'),
      single_mul_single_of_ne _ _ _ _ (lineCoord_swap_ne b).symm,
      single_mul_single_of_ne _ _ _ _ (lineCoord_swap_ne a),
      single_mul_single_of_ne _ _ _ _ hsw, sub_zero]

theorem uRootMat_mul {h : UnitaryFieldData p f K} {a b : Fin r ⊕ Fin r} (hab : a ≠ b)
    (s t : K) : uRootMat ε h a b s * uRootMat ε h a b t = uRootMat ε h a b (s + t) := by
  rw [uRootMat, uRootMat, uRootMat, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
    Matrix.mul_one, uRootNil_mul hab, add_zero, uRootNil_add]
  abel

theorem uRootMat_zero (h : UnitaryFieldData p f K) (a b : Fin r ⊕ Fin r) :
    uRootMat ε h a b 0 = 1 := by
  rw [uRootMat, uRootNil_zero, add_zero]

theorem mem_traceZero_add {h : UnitaryFieldData p f K} {t : K} (ht : t ∈ h.traceZero) :
    h.bar t + t = 0 := by
  have := (UnitaryFieldData.mem_traceZero h).mp ht
  rw [UnitaryFieldData.trace] at this
  rw [add_comm]
  exact this

theorem uRootNil_gram_add (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r} {t : K}
    (ht : t ∈ uRootDom h a b) :
    ((uRootNil ε h a b t).map h.bar)ᵀ * hypGram r ε K + hypGram r ε K * uRootNil ε h a b t =
      0 := by
  unfold uRootNil
  split_ifs with hb
  · subst hb
    rw [uRootDom_swap] at ht
    rw [conjTranspose_single, single_mul_hypGram, hypGram_mul_single, lineCoord_swap,
      ← single_add, mem_traceZero_add ht, single_zero]
  · rw [Matrix.map_sub _ (map_sub h.bar), transpose_sub, conjTranspose_single,
      conjTranspose_single, Matrix.sub_mul, Matrix.mul_sub, single_mul_hypGram,
      single_mul_hypGram, hypGram_mul_single, hypGram_mul_single, lineCoord_swap,
      lineCoord_swap, hypPartner_hypPartner, h.bar_bar]
    abel

theorem uRootNil_gram_mul (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r} (hab : a ≠ b)
    (t : K) :
    ((uRootNil ε h a b t).map h.bar)ᵀ * hypGram r ε K * uRootNil ε h a b t = 0 := by
  have hab' : lineCoord (ε := ε) a ≠ lineCoord b := fun h' => hab (lineCoord_injective h')
  have hsw : hypPartner (lineCoord (ε := ε) a) ≠ hypPartner (lineCoord b) := fun h' =>
    hab' (by simpa using congrArg hypPartner h')
  have hpa : hypPartner (lineCoord (ε := ε) a) ≠ lineCoord a := by
    rw [← lineCoord_swap]; exact lineCoord_swap_ne a
  have hpb : lineCoord (ε := ε) b ≠ hypPartner (lineCoord b) := by
    rw [← lineCoord_swap]; exact (lineCoord_swap_ne b).symm
  unfold uRootNil
  split_ifs with hb
  · rw [conjTranspose_single, single_mul_hypGram, single_mul_single_of_ne _ _ _ _ hpa]
  · rw [Matrix.map_sub _ (map_sub h.bar), transpose_sub, conjTranspose_single,
      conjTranspose_single, Matrix.sub_mul, single_mul_hypGram, single_mul_hypGram,
      lineCoord_swap, lineCoord_swap, hypPartner_hypPartner]
    simp only [Matrix.sub_mul, Matrix.mul_sub, single_mul_single_of_ne _ _ _ _ hpa,
      single_mul_single_of_ne _ _ _ _ hsw, single_mul_single_of_ne _ _ _ _ hab'.symm,
      single_mul_single_of_ne _ _ _ _ hpb, sub_zero]

theorem uRootMat_gram (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r} (hab : a ≠ b)
    {t : K} (ht : t ∈ uRootDom h a b) :
    ((uRootMat ε h a b t).map h.bar)ᵀ * hypGram r ε K * uRootMat ε h a b t = hypGram r ε K := by
  have h1 := uRootNil_gram_add (ε := ε) h ht
  have h2 := uRootNil_gram_mul (ε := ε) h hab t
  set N := uRootNil ε h a b t
  have hT : ((uRootMat ε h a b t).map h.bar)ᵀ = 1 + (N.map h.bar)ᵀ := by
    rw [uRootMat, Matrix.map_add _ (map_add h.bar), Matrix.map_one _ (map_zero _) (map_one _),
      transpose_add, transpose_one]
  have hexp : (1 + (N.map h.bar)ᵀ) * hypGram r ε K * (1 + N) = hypGram r ε K +
      ((N.map h.bar)ᵀ * hypGram r ε K + hypGram r ε K * N) +
      (N.map h.bar)ᵀ * hypGram r ε K * N := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [hT, uRootMat, hexp, h1, h2, add_zero, add_zero]

theorem det_uRootMat (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (t : K) :
    (uRootMat ε h a b t).det = 1 := by
  have hab' : lineCoord (ε := ε) a ≠ lineCoord b := fun h' => hab (lineCoord_injective h')
  have hsw : lineCoord (ε := ε) b.swap ≠ lineCoord a.swap := fun h' =>
    hab (SymplecticHigher.swap_injective' (lineCoord_injective h')).symm
  have hbb : lineCoord (ε := ε) b ≠ lineCoord b.swap := (lineCoord_swap_ne b).symm
  unfold uRootMat uRootNil
  split_ifs with hb
  · exact det_transvection_of_ne _ _ hab' t
  · have hfac : (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) +
        (single (lineCoord a) (lineCoord b) t - single (lineCoord b.swap) (lineCoord a.swap)
          (h.bar t)) =
        transvection (lineCoord a) (lineCoord b) t *
          transvection (lineCoord b.swap) (lineCoord a.swap) (-h.bar t) := by
      rw [transvection, transvection, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
        Matrix.mul_one, single_mul_single_of_ne _ _ _ _ hbb, add_zero, ← single_neg]
      abel
    rw [hfac, det_mul, det_transvection_of_ne _ _ hab', det_transvection_of_ne _ _ hsw, mul_one]


theorem uRootMat_partner (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r} (hb : b ≠ a.swap)
    (t : K) : uRootMat ε h b.swap a.swap t = uRootMat ε h a b (-h.bar t) := by
  have hb'' : ¬a.swap = b := fun h' => hb h'.symm
  simp only [uRootMat, uRootNil, hb, hb'', Sum.swap_swap, ↓reduceIte, map_neg, h.bar_bar]
  rw [← single_neg, ← single_neg]
  abel

@[expose] noncomputable def uRootElt (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r}
    (hab : a ≠ b) (t : uRootDom h a b) : hypSU h r ε :=
  ⟨⟨uRootMat ε h a b t, uRootMat ε h a b (-t : uRootDom h a b),
    by rw [uRootMat_mul hab, AddSubgroup.coe_neg, add_neg_cancel, uRootMat_zero],
    by rw [uRootMat_mul hab, AddSubgroup.coe_neg, neg_add_cancel, uRootMat_zero]⟩,
    mem_gramSU.mpr ⟨uRootMat_gram h hab t.2, det_uRootMat h hab t⟩⟩

theorem coe_uRootElt (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r} (hab : a ≠ b)
    (t : uRootDom h a b) :
    (((uRootElt (ε := ε) h hab t : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = uRootMat ε h a b t :=
  rfl

@[expose] noncomputable def uRootHom (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r}
    (hab : a ≠ b) : Multiplicative (uRootDom h a b) →* hypSU h r ε where
  toFun t := uRootElt h hab t.toAdd
  map_one' := Subtype.ext (Units.ext (by
    rw [coe_uRootElt, toAdd_one, AddSubgroup.coe_zero, uRootMat_zero]
    rfl))
  map_mul' s t := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_uRootElt, coe_uRootElt, coe_uRootElt, toAdd_mul,
      AddSubgroup.coe_add, uRootMat_mul hab]))


variable (ε) in
@[expose] noncomputable def uRootSubgroup (h : UnitaryFieldData p f K) (α : Fin r → ℤ) :
    Subgroup (hypSU h r ε) :=
  ⨆ q : {q : (Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) // q.1 ≠ q.2 ∧ rootVec q.1 q.2 = α},
    (uRootHom h q.2.1).range

theorem range_uRootHom_partner (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r}
    (hab : a ≠ b) (hab' : b.swap ≠ a.swap) :
    (uRootHom (ε := ε) h hab').range = (uRootHom h hab).range := by
  obtain ⟨φ, hφdom, hφsurj, hφmat⟩ : ∃ φ : K → K,
      (∀ t, t ∈ uRootDom h b.swap a.swap → φ t ∈ uRootDom h a b) ∧
      (∀ t ∈ uRootDom h a b, ∃ s ∈ uRootDom h b.swap a.swap, φ s = t) ∧
      ∀ t, uRootMat ε h b.swap a.swap t = uRootMat ε h a b (φ t) := by
    by_cases hb : b = a.swap
    · have hdom : uRootDom h b.swap a.swap = uRootDom h a b := by rw [hb, Sum.swap_swap]
      refine ⟨id, fun t ht => hdom ▸ ht, fun t ht => ⟨t, hdom ▸ ht, rfl⟩, fun t => ?_⟩
      rw [id, hb, Sum.swap_swap]
    · have hb' : a.swap ≠ b.swap.swap := by
        rw [Sum.swap_swap]
        exact fun h' => hb h'.symm
      refine ⟨fun t => -h.bar t, fun t _ => by rw [uRootDom_of_ne h hb]; trivial,
        fun t _ => ⟨-h.bar t, by rw [uRootDom_of_ne h hb']; trivial, by
          simp only [map_neg, h.bar_bar, neg_neg]⟩, fun t => uRootMat_partner h hb t⟩
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Multiplicative.ofAdd ⟨φ t.toAdd, hφdom _ t.toAdd.2⟩, Subtype.ext (Units.ext ?_)⟩
    change uRootMat ε h a b (φ t.toAdd) = uRootMat ε h b.swap a.swap t.toAdd
    rw [hφmat]
  · rintro ⟨t, rfl⟩
    obtain ⟨s, hs, hst⟩ := hφsurj t.toAdd t.toAdd.2
    refine ⟨Multiplicative.ofAdd ⟨s, hs⟩, Subtype.ext (Units.ext ?_)⟩
    change uRootMat ε h b.swap a.swap s = uRootMat ε h a b t.toAdd
    rw [hφmat, hst]

theorem uRootSubgroup_eq_range (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r}
    (hab : a ≠ b) : uRootSubgroup ε h (rootVec a b) = (uRootHom h hab).range := by
  refine le_antisymm (iSup_le fun q => ?_) (le_iSup_of_le ⟨(a, b), hab, rfl⟩ le_rfl)
  obtain ⟨⟨c, d⟩, hcd, hroot⟩ := q
  rcases (rootVec_eq_rootVec_iff hab hcd).mp hroot.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact le_rfl
  · exact (range_uRootHom_partner h hab hcd).le


theorem uRootMat_inl_inl (h : UnitaryFieldData p f K) {i j : Fin r} (t : K) :
    uRootMat ε h (.inl i) (.inl j) t =
      1 + single (.inl i) (.inl j) t - single (.inr (.inr j)) (.inr (.inr i)) (h.bar t) := by
  rw [uRootMat, uRootNil, ite_eq_right_iff.mpr (fun h' => absurd h' (by simp)), add_sub_assoc]
  rfl

theorem uRootMat_inl_inr (h : UnitaryFieldData p f K) {i j : Fin r} (hij : i ≠ j) (t : K) :
    uRootMat ε h (.inl i) (.inr j) t =
      1 + single (.inl i) (.inr (.inr j)) t - single (.inl j) (.inr (.inr i)) (h.bar t) := by
  have hne : (Sum.inr j : Fin r ⊕ Fin r) ≠ (Sum.inl i).swap := by simpa using hij.symm
  rw [uRootMat, uRootNil, ite_eq_right_iff.mpr (fun h' => absurd h' hne), add_sub_assoc]
  rfl


theorem uRootMat_inl_inr_self (h : UnitaryFieldData p f K) (i : Fin r) (t : K) :
    uRootMat ε h (.inl i) (.inr i) t = 1 + single (.inl i) (.inr (.inr i)) t := by
  rw [uRootMat, uRootNil, ite_eq_left (show Sum.inr i = (Sum.inl i).swap from rfl)]
  rfl

theorem uRootMat_inr_inl_self (h : UnitaryFieldData p f K) (i : Fin r) (t : K) :
    uRootMat ε h (.inr i) (.inl i) t = 1 + single (.inr (.inr i)) (.inl i) t := by
  rw [uRootMat, uRootNil, ite_eq_left (show Sum.inl i = (Sum.inr i).swap from rfl)]
  rfl

theorem inv_mem_traceZero {h : UnitaryFieldData p f K} {c : K} (hc : c ∈ h.traceZero) :
    c⁻¹ ∈ h.traceZero := by
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_inv₀]
  have hbc : h.bar c = -c := by
    have := mem_traceZero_add hc
    linear_combination this
  rw [hbc, inv_neg, add_neg_cancel]

theorem simpleSnd_of_lt {k : Fin r} (hk : (k : ℕ) + 1 < r) :
    simpleSnd k = .inl ⟨k + 1, hk⟩ := by
  simp [simpleSnd, hk]

theorem one_mem_uRootDom_simple (h : UnitaryFieldData p f K) {k : Fin r}
    (hk : (k : ℕ) + 1 < r) (t : K) : t ∈ uRootDom h (.inl k) (simpleSnd k) := by
  rw [uRootDom_of_ne h (by rw [simpleSnd_of_lt hk]; simp)]
  trivial

theorem one_mem_uRootDom_simple_symm (h : UnitaryFieldData p f K) {k : Fin r}
    (hk : (k : ℕ) + 1 < r) (t : K) : t ∈ uRootDom h (simpleSnd k) (.inl k) := by
  rw [uRootDom_of_ne h (by rw [simpleSnd_of_lt hk]; simp)]
  trivial

theorem inl_ne_inr (k : Fin r) : (Sum.inl k : Fin r ⊕ Fin r) ≠ .inr k := by simp

variable (ε) in
@[expose] noncomputable def uWeylRepShort (h : UnitaryFieldData p f K) (k : Fin r)
    (hk : (k : ℕ) + 1 < r) : hypSU h r ε :=
  uRootElt h (inl_ne_simpleSnd k) ⟨1, one_mem_uRootDom_simple h hk 1⟩ *
    uRootElt h (inl_ne_simpleSnd k).symm ⟨-1, one_mem_uRootDom_simple_symm h hk (-1)⟩ *
    uRootElt h (inl_ne_simpleSnd k) ⟨1, one_mem_uRootDom_simple h hk 1⟩

variable (ε) in
@[expose] noncomputable def uWeylRepLong (h : UnitaryFieldData p f K) (k : Fin r) (c : K)
    (hc : c ∈ h.traceZero) : hypSU h r ε :=
  uRootElt h (inl_ne_inr k) ⟨-c⁻¹, by
      rw [show (Sum.inr k : Fin r ⊕ Fin r) = (Sum.inl k).swap from rfl, uRootDom_swap]
      exact neg_mem (inv_mem_traceZero hc)⟩ *
    uRootElt h (inl_ne_inr k).symm ⟨c, by
      rw [show (Sum.inl k : Fin r ⊕ Fin r) = (Sum.inr k).swap from rfl, uRootDom_swap]
      exact hc⟩ *
    uRootElt h (inl_ne_inr k) ⟨-c⁻¹, by
      rw [show (Sum.inr k : Fin r ⊕ Fin r) = (Sum.inl k).swap from rfl, uRootDom_swap]
      exact neg_mem (inv_mem_traceZero hc)⟩


end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
