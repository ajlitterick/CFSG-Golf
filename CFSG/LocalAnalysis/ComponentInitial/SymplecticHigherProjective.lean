module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.ClassicalGroups.Alternating.Transvections

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def symplecticOfJ {n : ℕ} (b : Basis (Fin n ⊕ Fin n) K V) :
    Basis (Fin n ⊕ Fin n) K V :=
  b.unitsSMul (Sum.elim 1 (-1))

theorem symplecticOfJ_inl {n : ℕ} (b : Basis (Fin n ⊕ Fin n) K V) (i : Fin n) :
    symplecticOfJ b (Sum.inl i) = b (Sum.inl i) := by
  simp [symplecticOfJ, Basis.unitsSMul_apply]


theorem isSymplecticBasis_symplecticOfJ {n : ℕ} {B : BilinForm K V}
    (b : Basis (Fin n ⊕ Fin n) K V) (hb : ∀ x y, B (b x) (b y) = Matrix.J (Fin n) K x y) :
    IsSymplecticBasis B (symplecticOfJ b) := by
  ext (x | x) (y | y) <;>
    simp [symplecticOfJ, BilinForm.toMatrix_apply, Basis.unitsSMul_apply, hb, Matrix.J,
      Units.smul_def, Matrix.one_apply]

variable [FiniteDimensional K V] {B : BilinForm K V}

open CFSG.ComponentClassification.CatalogueBAlternatingIsometry in
theorem exists_isSymplecticBasis_pair (hB : B.IsAlt) (hnd : B.Nondegenerate) {a c : V}
    (hac : B a c = 1) :
    ∃ (m : ℕ) (b : Basis (Fin (m + 1) ⊕ Fin (m + 1)) K V), IsSymplecticBasis B b ∧
      b (Sum.inl 0) = a ∧ b (Sum.inr 0) = c := by
  obtain ⟨m, b, -, hee, hff, hef, hb1, hb2⟩ :=
    exists_symplectic_basis_prescribed_pair B hB hnd a c hac
  refine ⟨m, b, ?_, hb1, hb2⟩
  ext (x | x) (y | y)
  · simp [BilinForm.toMatrix_apply, hee]
  · simp [BilinForm.toMatrix_apply, hef, Matrix.one_apply]
  · rw [BilinForm.toMatrix_apply, ← hB.neg_eq, hef]
    simp [Matrix.one_apply, eq_comm]
  · simp [BilinForm.toMatrix_apply, hff]

theorem alternating_isotropic_pair_extension (hB : B.IsAlt) (hnd : B.Nondegenerate) {a₁ a₂ : V}
    (hli : LinearIndependent K ![a₁, a₂]) (h12 : B a₁ a₂ = 0) :
    ∃ (m : ℕ) (b : Basis (Fin (m + 2) ⊕ Fin (m + 2)) K V), IsSymplecticBasis B b ∧
      b (Sum.inl 0) = a₁ ∧ b (Sum.inl 1) = a₂ ∧ finrank K V = 2 * (m + 2) := by
  obtain ⟨x, hx⟩ := CFSG.ClassicalGroups.Alternating.alternating_pairing_surjectivity hnd hli
    ![1, 0]
  have hx1 : B a₁ x = 1 := by simpa using congrFun hx 0
  have hx2 : B a₂ x = 0 := by simpa using congrFun hx 1
  have hfe : B (-x) a₁ = 1 := by rw [map_neg, LinearMap.neg_apply, hB.neg_eq, hx1]
  set Z := B.orthogonal (span K {a₁, -x}) with hZdef
  have ha₂Z : a₂ ∈ Z := by
    rw [hZdef, BilinForm.mem_orthogonal_span_pair_iff]
    refine ⟨h12, ?_⟩
    rw [map_neg, LinearMap.neg_apply, hB.neg_eq, hx2]
  have ha₂0 : (⟨a₂, ha₂Z⟩ : Z) ≠ 0 := fun h => hli.ne_zero 1 (by
    have := congrArg Subtype.val h
    simpa using this)
  have hZalt : (B.restrict Z).IsAlt := fun z => hB.self_eq_zero z
  obtain ⟨m, c, hc, hc0⟩ := hZalt.exists_basis_apply_eq_J_inl_zero_eq
    (hB.restrict_nondegenerate_orthogonal_span_pair hfe hnd) ha₂0
  have hc' : ∀ x y, B (c x) (c y) = Matrix.J (Fin (m + 1)) K x y := fun x y => by
    rw [← hc x y, BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  obtain ⟨b, hb, hbd⟩ := hB.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair hnd hfe c hc'
  refine ⟨m, symplecticOfJ b, isSymplecticBasis_symplecticOfJ b hb, ?_, ?_, ?_⟩
  · rw [symplecticOfJ_inl, hbd]
    simp
  · rw [symplecticOfJ_inl, hbd]
    have : (1 : Fin (m + 2)) = Fin.succ 0 := rfl
    rw [this, Sum.elim_inl, Fin.cons_succ, hc0]
  · rw [finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin]
    ring

end Abstract

section Scalars

variable {r : ℕ} {K : Type} [Field K]

theorem spScalars_le_center : spScalars r K ≤ Subgroup.center (StatedSp r K) := by
  intro z hz
  rw [Subgroup.mem_subgroupOf, StatedScalars,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hz (g : GL (Fin r ⊕ Fin r) K))

end Scalars

section Points

variable {r : ℕ} {K : Type} [Field K]

variable (r K) in
@[ext] structure SpPoint where
  line : Submodule K (Fin r ⊕ Fin r → K)
  finrank_line : finrank K line = 1

theorem spAct_injective (g : StatedSp r K) : Function.Injective (spAct g) := by
  intro u v h
  have := congrArg (spAct g⁻¹) h
  simp only [spAct, mulVecLin_apply, mulVec_mulVec] at this
  rwa [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
    one_mulVec, one_mulVec] at this

theorem finrank_map_spAct (g : StatedSp r K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    finrank K (W.map (spAct g)) = finrank K W :=
  (Submodule.equivMapOfInjective _ (spAct_injective g) W).finrank_eq.symm

instance : MulAction (StatedSp r K) (SpPoint r K) where
  smul g L := ⟨L.line.map (spAct g), by rw [finrank_map_spAct]; exact L.finrank_line⟩
  one_smul L := SpPoint.ext (map_spAct_one L.line)
  mul_smul g h L := SpPoint.ext (map_spAct_mul g h L.line)

theorem line_smul (g : StatedSp r K) (L : SpPoint r K) :
    (g • L).line = L.line.map (spAct g) :=
  rfl

@[expose] def SpPoint.ofVec (v : Fin r ⊕ Fin r → K) (hv : v ≠ 0) : SpPoint r K :=
  ⟨span K {v}, finrank_span_singleton hv⟩

theorem line_ofVec (v : Fin r ⊕ Fin r → K) (hv : v ≠ 0) :
    (SpPoint.ofVec v hv).line = span K {v} :=
  rfl

theorem SpPoint.exists_ofVec (L : SpPoint r K) : ∃ (v : Fin r ⊕ Fin r → K) (hv : v ≠ 0),
    L = SpPoint.ofVec v hv := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp L.finrank_line
  refine ⟨v, fun h => hv0 (Subtype.ext h), SpPoint.ext ?_⟩
  apply le_antisymm
  · intro w hw
    obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
    rw [line_ofVec, mem_span_singleton]
    exact ⟨c, congrArg Subtype.val hc⟩
  · rw [SpPoint.ofVec, span_le, Set.singleton_subset_iff]
    exact v.2

theorem smul_ofVec (g : StatedSp r K) (v : Fin r ⊕ Fin r → K) (hv : v ≠ 0) :
    g • SpPoint.ofVec v hv = SpPoint.ofVec (spAct g v)
      (fun h => hv (spAct_injective g (h.trans (map_zero _).symm))) := by
  refine SpPoint.ext ?_
  rw [line_smul, line_ofVec, line_ofVec, Submodule.map_span, Set.image_singleton]

theorem ofVec_smul_eq {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) {c : K} (hc : c ≠ 0)
    (hcv : c • v ≠ 0) : SpPoint.ofVec (c • v) hcv = SpPoint.ofVec v hv :=
  SpPoint.ext (span_singleton_smul_eq (IsUnit.mk0 c hc) v)

@[expose] def SpOrth (L M : SpPoint r K) : Prop :=
  ∀ x ∈ L.line, ∀ y ∈ M.line, pairedSympForm K r x y = 0

theorem spOrth_ofVec_iff {u v : Fin r ⊕ Fin r → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    SpOrth (SpPoint.ofVec u hu) (SpPoint.ofVec v hv) ↔ pairedSympForm K r u v = 0 := by
  constructor
  · intro h
    exact h u (mem_span_singleton_self u) v (mem_span_singleton_self v)
  · intro h x hx y hy
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := mem_span_singleton.mp hy
    rw [map_smul, map_smul, LinearMap.smul_apply, h, smul_zero, smul_zero]

theorem spOrth_smul_iff (g : StatedSp r K) {L M : SpPoint r K} :
    SpOrth (g • L) (g • M) ↔ SpOrth L M := by
  obtain ⟨u, hu, rfl⟩ := L.exists_ofVec
  obtain ⟨v, hv, rfl⟩ := M.exists_ofVec
  rw [smul_ofVec, smul_ofVec, spOrth_ofVec_iff, spOrth_ofVec_iff]
  exact iff_of_eq (congrArg (· = (0 : K)) (pairedSympForm_mulVec g u v))

theorem spOrth_comm {L M : SpPoint r K} : SpOrth L M ↔ SpOrth M L := by
  obtain ⟨u, hu, rfl⟩ := L.exists_ofVec
  obtain ⟨v, hv, rfl⟩ := M.exists_ofVec
  rw [spOrth_ofVec_iff, spOrth_ofVec_iff, ← pairedSympForm_isAlt.neg_eq, neg_eq_zero]

theorem spOrth_self (L : SpPoint r K) : SpOrth L L := by
  obtain ⟨u, hu, rfl⟩ := L.exists_ofVec
  rw [spOrth_ofVec_iff]
  exact pairedSympForm_self u

theorem isTotallyIsotropic_line (L : SpPoint r K) :
    IsTotallyIsotropic (pairedSympForm K r) L.line :=
  fun x hx y hy => spOrth_self L x hx y hy

theorem ofVec_ne_of_spOrth {L M : SpPoint r K} (hL : SpOrth L L) (hM : ¬SpOrth L M) : L ≠ M :=
  fun h => hM (h ▸ hL)

theorem linearIndependent_of_ofVec_ne {u v : Fin r ⊕ Fin r → K} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : SpPoint.ofVec u hu ≠ SpPoint.ofVec v hv) : LinearIndependent K ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hu, ht⟩
  · exfalso
    have hv' : v = (-(t⁻¹ * s)) • u := by
      have : t • v = -(s • u) := eq_neg_of_add_eq_zero_right hst
      rw [neg_smul, mul_smul, ← smul_neg, ← this, smul_smul, inv_mul_cancel₀ ht, one_smul]
    have hc : -(t⁻¹ * s) ≠ 0 := fun h0 => hv (by rw [hv', h0, zero_smul])
    apply h
    rw [← ofVec_smul_eq hu hc (by rw [← hv']; exact hv)]
    exact SpPoint.ext (by rw [line_ofVec, line_ofVec, hv'])

theorem exists_smul_eq_point (L M : SpPoint r K) : ∃ g : StatedSp r K, g • L = M := by
  obtain ⟨g, hg⟩ := exists_statedSp_map_eq (isTotallyIsotropic_line L) (isTotallyIsotropic_line M)
    (by rw [L.finrank_line, M.finrank_line])
  exact ⟨g, SpPoint.ext hg⟩

theorem exists_smul_eq_of_bases {b b' : Basis (Fin r ⊕ Fin r) K (Fin r ⊕ Fin r → K)}
    (hb : IsSymplecticBasis (pairedSympForm K r) b)
    (hb' : IsSymplecticBasis (pairedSympForm K r) b') :
    ∃ g : StatedSp r K, ∀ x, spAct g (b x) = b' x := by
  obtain ⟨g, hg⟩ := exists_statedSp_mulVec_basis hb hb'
  exact ⟨g, hg⟩

theorem exists_smul_pair_of_not_spOrth {u v u' v' : Fin r ⊕ Fin r → K} (hu : u ≠ 0) (hv : v ≠ 0)
    (hu' : u' ≠ 0) (hv' : v' ≠ 0) (h : pairedSympForm K r u v ≠ 0)
    (h' : pairedSympForm K r u' v' ≠ 0) :
    ∃ g : StatedSp r K, g • SpPoint.ofVec u hu = SpPoint.ofVec u' hu' ∧
      g • SpPoint.ofVec v hv = SpPoint.ofVec v' hv' := by
  set c := (pairedSympForm K r u v)⁻¹
  set c' := (pairedSympForm K r u' v')⁻¹
  have hc : c ≠ 0 := inv_ne_zero h
  have hc' : c' ≠ 0 := inv_ne_zero h'
  have h1 : pairedSympForm K r u (c • v) = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ h]
  have h1' : pairedSympForm K r u' (c' • v') = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ h']
  obtain ⟨m, b, hb, hb1, hb2⟩ := exists_isSymplecticBasis_pair pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate h1
  obtain ⟨m', b', hb', hb1', hb2'⟩ := exists_isSymplecticBasis_pair pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate h1'
  have hm : m + 1 = r := by
    have := finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    rw [finrank_standard] at this
    omega
  have hm' : m' = m := by
    have := finrank_eq_card_basis b'
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    rw [finrank_standard] at this
    omega
  subst hm hm'
  obtain ⟨g, hg⟩ := exists_smul_eq_of_bases hb hb'
  refine ⟨g, ?_, ?_⟩
  · rw [smul_ofVec]
    exact SpPoint.ext (by rw [line_ofVec, line_ofVec, ← hb1, hg, hb1'])
  · have hcv : c • v ≠ 0 := smul_ne_zero hc hv
    have hcv' : c' • v' ≠ 0 := smul_ne_zero hc' hv'
    rw [← ofVec_smul_eq hv hc hcv, ← ofVec_smul_eq hv' hc' hcv', smul_ofVec]
    exact SpPoint.ext (by rw [line_ofVec, line_ofVec, ← hb2, hg, hb2'])

theorem exists_smul_pair_of_spOrth {u v u' v' : Fin r ⊕ Fin r → K} (hu : u ≠ 0) (hv : v ≠ 0)
    (hu' : u' ≠ 0) (hv' : v' ≠ 0) (hne : SpPoint.ofVec u hu ≠ SpPoint.ofVec v hv)
    (hne' : SpPoint.ofVec u' hu' ≠ SpPoint.ofVec v' hv') (h : pairedSympForm K r u v = 0)
    (h' : pairedSympForm K r u' v' = 0) :
    ∃ g : StatedSp r K, g • SpPoint.ofVec u hu = SpPoint.ofVec u' hu' ∧
      g • SpPoint.ofVec v hv = SpPoint.ofVec v' hv' := by
  have hli := linearIndependent_of_ofVec_ne hu hv hne
  have hli' := linearIndependent_of_ofVec_ne hu' hv' hne'
  obtain ⟨m, b, hb, hb1, hb2, hdim⟩ := alternating_isotropic_pair_extension
    (V := Fin r ⊕ Fin r → K) (B := pairedSympForm K r) (a₁ := u) (a₂ := v)
    SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate hli h
  obtain ⟨m', b', hb', hb1', hb2', hdim'⟩ := alternating_isotropic_pair_extension
    (V := Fin r ⊕ Fin r → K) (B := pairedSympForm K r) (a₁ := u') (a₂ := v')
    SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate hli' h'
  have hm : m + 2 = r := by rw [finrank_standard] at hdim; omega
  have hm' : m' = m := by rw [finrank_standard] at hdim'; omega
  subst hm hm'
  obtain ⟨g, hg⟩ := exists_smul_eq_of_bases hb hb'
  refine ⟨g, ?_, ?_⟩
  · rw [smul_ofVec]
    exact SpPoint.ext (by rw [line_ofVec, line_ofVec, ← hb1, hg, hb1'])
  · rw [smul_ofVec]
    exact SpPoint.ext (by rw [line_ofVec, line_ofVec, ← hb2, hg, hb2'])

theorem exists_smul_pair_iff {L M L' M' : SpPoint r K} (hLM : L ≠ M) (hLM' : L' ≠ M') :
    (∃ g : StatedSp r K, g • L = L' ∧ g • M = M') ↔ (SpOrth L M ↔ SpOrth L' M') := by
  constructor
  · rintro ⟨g, rfl, rfl⟩
    exact (spOrth_smul_iff g).symm
  · intro h
    obtain ⟨u, hu, rfl⟩ := L.exists_ofVec
    obtain ⟨v, hv, rfl⟩ := M.exists_ofVec
    obtain ⟨u', hu', rfl⟩ := L'.exists_ofVec
    obtain ⟨v', hv', rfl⟩ := M'.exists_ofVec
    rw [spOrth_ofVec_iff, spOrth_ofVec_iff] at h
    by_cases h0 : pairedSympForm K r u v = 0
    · exact exists_smul_pair_of_spOrth hu hv hu' hv' hLM hLM' h0 (h.mp h0)
    · exact exists_smul_pair_of_not_spOrth hu hv hu' hv' h0 (fun h1 => h0 (h.mpr h1))

theorem not_spOrth_of_ne_of_rank_one (hr : r = 1) {L M : SpPoint r K} (hLM : L ≠ M) :
    ¬SpOrth L M := by
  intro horth
  obtain ⟨u, hu, rfl⟩ := L.exists_ofVec
  obtain ⟨v, hv, rfl⟩ := M.exists_ofVec
  have h0 := (spOrth_ofVec_iff hu hv).mp horth
  have hli := linearIndependent_of_ofVec_ne hu hv hLM
  have hiso : IsTotallyIsotropic (pairedSympForm K r) (span K {u, v}) := by
    intro x hx y hy
    obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hx
    obtain ⟨c, d, rfl⟩ := mem_span_pair.mp hy
    have h0' : pairedSympForm K r v u = 0 := by
      rw [← pairedSympForm_isAlt.neg_eq, h0, neg_zero]
    simp [map_add, map_smul, h0, h0', pairedSympForm_self]
  have h2 : finrank K (span K {u, v}) = 2 := by
    rw [← Matrix.range_cons_cons_empty u v ![], finrank_span_eq_card hli, Fintype.card_fin]
  have := finrank_le_of_isTotallyIsotropic pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate finrank_standard hiso
  omega

theorem single_ne_zero (x : Fin r ⊕ Fin r) : (Pi.single x (1 : K) : Fin r ⊕ Fin r → K) ≠ 0 :=
  fun h => one_ne_zero (α := K) (by simpa using congrFun h x)

theorem symplectic_projective_orbits :
    MulAction.IsPretransitive (StatedSp r K) (SpPoint r K) ∧
    (∀ L M L' M' : SpPoint r K, L ≠ M → L' ≠ M' →
      ((∃ g : StatedSp r K, g • L = L' ∧ g • M = M') ↔ (SpOrth L M ↔ SpOrth L' M'))) ∧
    (r = 1 → ∀ L M : SpPoint r K, L ≠ M → ¬SpOrth L M) ∧
    (2 ≤ r → (∃ L M : SpPoint r K, L ≠ M ∧ SpOrth L M) ∧
      ∃ L M : SpPoint r K, L ≠ M ∧ ¬SpOrth L M) := by
  refine ⟨⟨fun L M => exists_smul_eq_point L M⟩, fun L M L' M' h h' => exists_smul_pair_iff h h',
    fun hr L M h => not_spOrth_of_ne_of_rank_one hr h, fun hr => ?_⟩
  set i₀ : Fin r := ⟨0, by omega⟩
  set i₁ : Fin r := ⟨1, by omega⟩
  have horth : SpOrth (SpPoint.ofVec _ (single_ne_zero (K := K) (Sum.inl i₀)))
      (SpPoint.ofVec _ (single_ne_zero (K := K) (Sum.inl i₁))) := by
    rw [spOrth_ofVec_iff, pairedSympForm_single_inl]
    simp
  have hnorth : ¬SpOrth (SpPoint.ofVec _ (single_ne_zero (K := K) (Sum.inl i₀)))
      (SpPoint.ofVec _ (single_ne_zero (K := K) (Sum.inr i₀))) := by
    rw [spOrth_ofVec_iff, pairedSympForm_single_inl]
    simp
  refine ⟨⟨_, _, fun h => ?_, horth⟩, ⟨_, _, ofVec_ne_of_spOrth (spOrth_self _) hnorth, hnorth⟩⟩
  have := congrArg SpPoint.line h
  rw [line_ofVec, line_ofVec] at this
  have hmem : (Pi.single (Sum.inl i₁) (1 : K) : Fin r ⊕ Fin r → K) ∈
      span K {(Pi.single (Sum.inl i₀) (1 : K) : Fin r ⊕ Fin r → K)} := by
    rw [this]
    exact mem_span_singleton_self _
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hmem
  have := congrFun hc (Sum.inl i₁)
  simp [i₀, i₁] at this

end Points

section Primitive

open scoped Pointwise

variable {r : ℕ} {K : Type} [Field K]


end Primitive

section Kernel

variable {r : ℕ} {K : Type} [Field K]

theorem exists_scalar_of_forall_smul_eq {g : StatedSp r K} (h : ∀ L : SpPoint r K, g • L = L) :
    ∃ c : Kˣ, (g : GL (Fin r ⊕ Fin r) K) = Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  have hcol : ∀ v : Fin r ⊕ Fin r → K, ¬LinearIndependent K ![v, spAct g v] := by
    intro v hv
    by_cases hv0 : v = 0
    · exact hv.ne_zero 0 (by simp [hv0])
    have hL := h (SpPoint.ofVec v hv0)
    rw [smul_ofVec] at hL
    have hmem : spAct g v ∈ span K {v} := by
      have := congrArg SpPoint.line hL
      rw [line_ofVec, line_ofVec] at this
      rw [← this]
      exact mem_span_singleton_self _
    obtain ⟨a, ha⟩ := mem_span_singleton.mp hmem
    rw [LinearIndependent.pair_iff] at hv
    have := hv a (-1) (by rw [← ha]; simp)
    exact absurd this.2 (by norm_num)
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hcol
  have hA : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      Matrix.scalar (Fin r ⊕ Fin r) a := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    have := LinearMap.congr_fun ha v
    change spAct g v = _ at this
    rw [spAct, mulVecLin_apply] at this
    rw [this, scalar_apply]
    ext x
    simp [mulVec_diagonal]
  rcases isEmpty_or_nonempty (Fin r ⊕ Fin r) with hn | hn
  · exact ⟨1, Subsingleton.elim _ _⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin r ⊕ Fin r) K).isUnit
    rw [hA, map_zero, Matrix.det_zero] at hdet
    exact not_isUnit_zero hdet
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, hA]
  rfl

theorem ker_toPermHom_spPoint :
    (MulAction.toPermHom (StatedSp r K) (SpPoint r K)).ker = spScalars r K := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    have h : ∀ L : SpPoint r K, g • L = L := fun L => by
      have := congrArg (fun σ : Equiv.Perm (SpPoint r K) => σ L) hg
      simpa using this
    obtain ⟨c, hc⟩ := exists_scalar_of_forall_smul_eq h
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    exact ⟨c, hc.symm⟩
  · intro hg
    refine Equiv.ext fun L => ?_
    change g • L = L
    exact SpPoint.ext (mem_stabilizer.mp (spScalars_le_stabilizer L.line hg))

variable (r K) in
@[expose] def projPointHom : StatedProj (StatedSp r K) →* Equiv.Perm (SpPoint r K) :=
  QuotientGroup.lift (spScalars r K) (MulAction.toPermHom (StatedSp r K) (SpPoint r K))
    (le_of_eq ker_toPermHom_spPoint.symm)

instance : MulAction (StatedProj (StatedSp r K)) (SpPoint r K) :=
  MulAction.compHom _ (projPointHom r K)

theorem proj_smul_spPoint (g : StatedSp r K) (L : SpPoint r K) : proj r K g • L = g • L :=
  rfl

instance : FaithfulSMul (StatedProj (StatedSp r K)) (SpPoint r K) where
  eq_of_smul_eq_smul {p₁ p₂} h := by
    obtain ⟨g₁, rfl⟩ := proj_surjective p₁
    obtain ⟨g₂, rfl⟩ := proj_surjective p₂
    have hker : g₁⁻¹ * g₂ ∈ spScalars r K := by
      rw [← ker_toPermHom_spPoint, MonoidHom.mem_ker]
      refine Equiv.ext fun L => ?_
      change (g₁⁻¹ * g₂) • L = L
      rw [mul_smul, ← proj_smul_spPoint g₂, ← h L, proj_smul_spPoint, inv_smul_smul]
    exact (QuotientGroup.eq).mpr hker


end Kernel

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
