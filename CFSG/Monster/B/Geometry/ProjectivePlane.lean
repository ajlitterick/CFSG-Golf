module

public import CFSG.Monster.B.Geometry.ProjectivePlaneStab
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Monster.B.Geometry

open Module Submodule ProjPlane

variable {k : Type*} [Field k]

theorem planeDiagFun_single (a b : kˣ) (σ : k ≃+* k) (i : Fin 3) :
    ∃ u : k, u ≠ 0 ∧ planeDiagFun a b σ (Pi.single i 1) = u • Pi.single i 1 := by
  fin_cases i
  · refine ⟨a, a.ne_zero, ?_⟩
    ext j
    fin_cases j <;> simp [planeDiagFun]
  · refine ⟨b, b.ne_zero, ?_⟩
    ext j
    fin_cases j <;> simp [planeDiagFun]
  · refine ⟨1, one_ne_zero, ?_⟩
    ext j
    fin_cases j <;> simp [planeDiagFun]

namespace ProjPlane

theorem map_span_pair {σ : k →+* k} [RingHomSurjective σ]
    (φ : (Fin 3 → k) →ₛₗ[σ] (Fin 3 → k)) (u w : Fin 3 → k) :
    (span k {u, w}).map φ = span k {φ u, φ w} := by
  rw [Submodule.map_span, Set.image_pair]

theorem span_pair_smul {u w : Fin 3 → k} {α β : k} (hα : α ≠ 0) (hβ : β ≠ 0) :
    span k {α • u, β • w} = span k {u, w} := by
  rw [span_insert, span_insert, span_singleton_smul_eq (IsUnit.mk0 α hα),
    span_singleton_smul_eq (IsUnit.mk0 β hβ)]

end ProjPlane

theorem planeDiagPerm_apply_of_mem_apartment (a b : kˣ) (σ : k ≃+* k) {x : PlaneFlag k}
    (hx : x ∈ planeApartment k) : planeDiagPerm a b σ x = x := by
  obtain ⟨i, j, -, hpt, hline⟩ := hx
  obtain ⟨u, hu, hui⟩ := planeDiagFun_single a b σ i
  obtain ⟨w, hw, hwj⟩ := planeDiagFun_single a b σ j
  refine PlaneFlag.ext ?_ ?_
  · rw [planeDiagPerm_pt, hpt, map_span_singleton, planeDiagSemilin_apply, hui,
      span_singleton_smul_eq (IsUnit.mk0 u hu)]
  · rw [planeDiagPerm_line, hline, map_span_pair, planeDiagSemilin_apply,
      planeDiagSemilin_apply, hui, hwj, span_pair_smul hu hw]

theorem c_mem_planeApartment : PlaneFlag.c k ∈ planeApartment k :=
  ⟨0, 1, by decide, rfl, rfl⟩

theorem d_mem_planeApartment : PlaneFlag.d k ∈ planeApartment k := by
  refine ⟨2, 1, by decide, rfl, ?_⟩
  change span k {Pi.single 1 1, Pi.single 2 1} = span k {Pi.single 2 1, Pi.single 1 1}
  rw [Set.pair_comm]

theorem planeDiagPerm_mem_planeOppStab (a b : kˣ) (σ : k ≃+* k) :
    planeDiagPerm a b σ ∈ planeOppStab k :=
  mem_planePairStab.mpr ⟨planeDiagPerm_mem_planeTypeAut a b σ,
    planeDiagPerm_apply_of_mem_apartment a b σ c_mem_planeApartment,
    planeDiagPerm_apply_of_mem_apartment a b σ d_mem_planeApartment⟩


theorem planeDiagPerm_injective :
    Function.Injective fun p : kˣ × kˣ × (k ≃+* k) => planeDiagPerm p.1 p.2.1 p.2.2 := by
  rintro ⟨a, b, σ⟩ ⟨a', b', σ'⟩ h
  simp only at h
  have hpt : ∀ v : Fin 3 → k, v ≠ 0 → k ∙ planeDiagFun a b σ v = k ∙ planeDiagFun a' b' σ' v := by
    intro v hv
    rw [← ptMap_planeDiagPerm a b σ hv, ← ptMap_planeDiagPerm a' b' σ' hv, h]
  have ha : (a : k) = a' := by
    have := hpt ![1, 0, 1] (vec_ne_zero_of_two one_ne_zero)
    simp only [planeDiagFun_vec, map_one, map_zero, mul_one, mul_zero] at this
    exact (vec_eq_of_span_eq one_ne_zero this).1
  have hb : (b : k) = b' := by
    have := hpt ![0, 1, 1] (vec_ne_zero_of_two one_ne_zero)
    simp only [planeDiagFun_vec, map_one, map_zero, mul_one, mul_zero] at this
    exact (vec_eq_of_span_eq one_ne_zero this).2
  have hσ : ∀ t, σ t = σ' t := by
    intro t
    have := hpt ![t, 0, 1] (vec_ne_zero_of_two one_ne_zero)
    simp only [planeDiagFun_vec, map_one, map_zero, mul_zero] at this
    have h' := (vec_eq_of_span_eq one_ne_zero this).1
    rw [ha] at h'
    exact mul_left_cancel₀ a'.ne_zero h'
  simp only [Prod.mk.injEq]
  exact ⟨Units.ext ha, Units.ext hb, RingEquiv.ext hσ⟩

theorem existsUnique_planeDiagPerm_eq {g : Equiv.Perm (PlaneFlag k)} (hg : g ∈ planeOppStab k) :
    ∃! p : kˣ × kˣ × (k ≃+* k), planeDiagPerm p.1 p.2.1 p.2.2 = g := by
  obtain ⟨hg, hc, hd⟩ := mem_planePairStab.mp hg
  obtain ⟨a, b, σ, h⟩ := exists_planeDiagPerm_eq hg hc hd
  exact ⟨(a, b, σ), h, fun p hp => planeDiagPerm_injective (hp.trans h.symm)⟩

noncomputable def planeOppStabEquiv : kˣ × kˣ × (k ≃+* k) ≃ planeOppStab k :=
  Equiv.ofBijective (fun p => ⟨planeDiagPerm p.1 p.2.1 p.2.2, planeDiagPerm_mem_planeOppStab _ _ _⟩)
    ⟨fun _ _ h => planeDiagPerm_injective (congrArg Subtype.val h), fun g => by
      obtain ⟨p, hp, -⟩ := existsUnique_planeDiagPerm_eq g.2
      exact ⟨p, Subtype.ext hp⟩⟩

theorem nat_card_planeOppStab :
    Nat.card (planeOppStab k) = Nat.card kˣ * (Nat.card kˣ * Nat.card (k ≃+* k)) := by
  rw [← Nat.card_congr (planeOppStabEquiv (k := k)), Nat.card_prod, Nat.card_prod]

theorem planeDiagFun_one (v : Fin 3 → k) : planeDiagFun 1 1 (RingEquiv.refl k) v = v := by
  ext i
  fin_cases i <;> simp [planeDiagFun]

theorem planeDiagPerm_one : planeDiagPerm 1 1 (RingEquiv.refl k) = 1 := by
  have hmap : ∀ P : Submodule k (Fin 3 → k),
      P.map (planeDiagSemilin 1 1 (RingEquiv.refl k)) = P := by
    intro P
    ext v
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rwa [planeDiagSemilin_apply, planeDiagFun_one]
    · intro hv
      exact ⟨v, hv, by rw [planeDiagSemilin_apply, planeDiagFun_one]⟩
  ext1 x
  exact PlaneFlag.ext (hmap x.pt) (hmap x.line)


namespace ProjPlane

@[expose] def lineFlag (t : k) : PlaneFlag k :=
  ⟨k ∙ ![1, t, 0], kerLine 0 0 1, fr_inf t, fr_ker2 one_ne_zero, vec_le_kerLine.mpr (by ring)⟩

@[expose] def pointFlag (t : k) : PlaneFlag k :=
  ⟨k ∙ ![1, 0, 0], kerLine 0 t (-1), fr_inf 0, fr_ker2 (neg_ne_zero.mpr one_ne_zero),
    vec_le_kerLine.mpr (by ring)⟩


theorem lineFlag_injective : Function.Injective (lineFlag (k := k)) := fun _ _ h =>
  (vec_eq_of_span_eq' one_ne_zero (congrArg PlaneFlag.pt h)).1

theorem pointFlag_injective : Function.Injective (pointFlag (k := k)) := fun s t h => by
  have hl : kerLine 0 s (-1) = kerLine 0 t (-1) := congrArg PlaneFlag.line h
  have hmem : (![0, 1, s] : Fin 3 → k) ∈ kerLine 0 s (-1) := by
    rw [mem_kerLine]
    simp
  rw [hl, mem_kerLine] at hmem
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hmem
  linear_combination -hmem

theorem lineFlag_mem_linePanel (t : k) : lineFlag t ∈ (PlaneFlag.c k).linePanel :=
  (PlaneFlag.c_line (k := k)).symm

theorem pointFlag_mem_pointPanel (t : k) : pointFlag t ∈ (PlaneFlag.c k).pointPanel :=
  (PlaneFlag.c_pt (k := k)).symm


theorem not_vec_le_kerLine_100 {x y z : k} (hx : x ≠ 0) :
    ¬ k ∙ (![x, y, z] : Fin 3 → k) ≤ kerLine 1 0 0 := by
  rw [vec_le_kerLine]
  simpa using hx


theorem planeDiagPerm_lineFlag (a b : kˣ) (σ : k ≃+* k) (t : k) :
    planeDiagPerm a b σ (lineFlag t) = lineFlag ((a : k)⁻¹ * b * σ t) := by
  have hc := congrArg PlaneFlag.line
    (planeDiagPerm_apply_of_mem_apartment a b σ (c_mem_planeApartment (k := k)))
  rw [planeDiagPerm_line, PlaneFlag.c_line] at hc
  refine PlaneFlag.ext ?_ hc
  change (k ∙ ![1, t, 0]).map (planeDiagSemilin a b σ) = k ∙ ![1, (a : k)⁻¹ * b * σ t, 0]
  rw [map_span_singleton, planeDiagSemilin_apply, planeDiagFun_vec, map_one, map_zero, mul_one]
  refine span_eq_span_of_eq_smul a.ne_zero ?_
  ext i
  fin_cases i <;> simp [mul_assoc]

theorem planeDiagPerm_pointFlag (a b : kˣ) (σ : k ≃+* k) (t : k) :
    planeDiagPerm a b σ (pointFlag t) = pointFlag ((b : k)⁻¹ * σ t) := by
  have hc := congrArg PlaneFlag.pt
    (planeDiagPerm_apply_of_mem_apartment a b σ (c_mem_planeApartment (k := k)))
  rw [planeDiagPerm_pt, PlaneFlag.c_pt] at hc
  refine PlaneFlag.ext hc ?_
  change (kerLine 0 t (-1)).map (planeDiagSemilin a b σ) = kerLine 0 ((b : k)⁻¹ * σ t) (-1)
  have h1 : k ∙ ![(a : k), 0, 0] ≤ (kerLine 0 t (-1)).map (planeDiagSemilin a b σ) := by
    have : (k ∙ ![(1 : k), 0, 0]).map (planeDiagSemilin a b σ) ≤
        (kerLine 0 t (-1)).map (planeDiagSemilin a b σ) := map_mono (vec_le_kerLine.mpr (by ring))
    rwa [map_span_singleton, planeDiagSemilin_apply, planeDiagFun_vec, map_one, map_zero, mul_one,
      mul_zero] at this
  have h2 : k ∙ ![0, (b : k), σ t] ≤ (kerLine 0 t (-1)).map (planeDiagSemilin a b σ) := by
    have : (k ∙ ![(0 : k), 1, t]).map (planeDiagSemilin a b σ) ≤
        (kerLine 0 t (-1)).map (planeDiagSemilin a b σ) := map_mono (vec_le_kerLine.mpr (by ring))
    rwa [map_span_singleton, planeDiagSemilin_apply, planeDiagFun_vec, map_one, map_zero, mul_one,
      mul_zero] at this
  have hfr : finrank k ((kerLine 0 t (-1)).map (planeDiagSemilin a b σ)) = 2 := by
    rw [finrank_map_semilinear _ (planeDiagSemilin_bijective a b σ).1]
    exact fr_ker2 (neg_ne_zero.mpr one_ne_zero)
  refine line_eq_of_ne (fr_vec0 a.ne_zero) (fr_vec1 b.ne_zero) hfr
    (fr_ker2 (neg_ne_zero.mpr one_ne_zero))
    (ne_of_not_le_of_le (L := kerLine 1 0 0) (not_vec_le_kerLine_100 a.ne_zero)
      (vec_le_kerLine.mpr (by ring))) h1 h2 (vec_le_kerLine.mpr (by ring))
    (vec_le_kerLine.mpr ?_)
  field_simp
  ring

end ProjPlane

theorem eq_one_of_mem_planeOppStab_of_forall_panel {g : Equiv.Perm (PlaneFlag k)}
    (hg : g ∈ planeOppStab k)
    (h : ∀ x ∈ (PlaneFlag.c k).pointPanel ∪ (PlaneFlag.c k).linePanel, g x = x) : g = 1 := by
  obtain ⟨⟨a, b, σ⟩, rfl, -⟩ := existsUnique_planeDiagPerm_eq hg
  simp only at h ⊢
  have hline : ∀ t : k, (a : k)⁻¹ * b * σ t = t := fun t => by
    have := h (lineFlag t) (Or.inr (lineFlag_mem_linePanel t))
    rw [planeDiagPerm_lineFlag] at this
    exact lineFlag_injective this
  have hpoint : (b : k)⁻¹ * σ 1 = 1 := by
    have := h (pointFlag 1) (Or.inl (pointFlag_mem_pointPanel 1))
    rw [planeDiagPerm_pointFlag] at this
    exact pointFlag_injective this
  have hb : (b : k) = 1 := by
    rw [map_one, mul_one, inv_eq_one] at hpoint
    exact hpoint
  have ha : (a : k) = 1 := by
    have := hline 1
    rw [map_one, mul_one, hb, mul_one, inv_eq_one] at this
    exact this
  have hσ : ∀ t, σ t = t := fun t => by
    have := hline t
    rwa [ha, hb, inv_one, one_mul, one_mul] at this
  have hab : (a, b, σ) = ((1 : kˣ), (1 : kˣ), RingEquiv.refl k) := by
    simp only [Prod.mk.injEq]
    exact ⟨Units.ext ha, Units.ext hb, RingEquiv.ext hσ⟩
  simp only [Prod.mk.injEq] at hab
  rw [hab.1, hab.2.1, hab.2.2]
  exact planeDiagPerm_one

namespace ProjPlane

noncomputable def glOfLinearEquiv (T : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) : GL (Fin 3) k :=
  ⟨LinearMap.toMatrix' (T : (Fin 3 → k) →ₗ[k] (Fin 3 → k)),
    LinearMap.toMatrix' (T.symm : (Fin 3 → k) →ₗ[k] (Fin 3 → k)),
    by rw [← LinearMap.toMatrix'_comp, show (T : (Fin 3 → k) →ₗ[k] (Fin 3 → k)) ∘ₗ
      (T.symm : (Fin 3 → k) →ₗ[k] (Fin 3 → k)) = LinearMap.id from
        LinearMap.ext fun v => T.apply_symm_apply v, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, show (T.symm : (Fin 3 → k) →ₗ[k] (Fin 3 → k)) ∘ₗ
      (T : (Fin 3 → k) →ₗ[k] (Fin 3 → k)) = LinearMap.id from
        LinearMap.ext fun v => T.symm_apply_apply v, LinearMap.toMatrix'_id]⟩

theorem mulVecLin_glOfLinearEquiv (T : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) (v : Fin 3 → k) :
    Matrix.mulVecLin ((glOfLinearEquiv T : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) v = T v := by
  rw [Matrix.mulVecLin_apply]
  exact LinearMap.toMatrix'_mulVec _ v

end ProjPlane

theorem exists_planeGLPerm_of_isOpposite {x y : PlaneFlag k} (hxy : x.IsOpposite y) :
    ∃ A : GL (Fin 3) k, planeGLPerm A x = PlaneFlag.c k ∧ planeGLPerm A y = PlaneFlag.d k := by
  obtain ⟨hxy1, hxy2⟩ := hxy
  obtain ⟨w, hw0, hwx, hwy⟩ := exists_mem_inf x.finrank_line y.finrank_line
  obtain ⟨u, hu0, hu⟩ := exists_eq_span x.finrank_pt
  obtain ⟨v, hv0, hv⟩ := exists_eq_span y.finrank_pt
  have hux : u ∈ x.line := x.pt_le_line (hu ▸ mem_span_singleton_self u)
  have hw1 : finrank k (k ∙ w) = 1 := finrank_span_singleton hw0
  have hne1 : x.pt ≠ k ∙ w := fun h => hxy1 (h ▸ (span_singleton_le_iff_mem w _).mpr hwy)
  have hne2 : k ∙ w ≠ y.pt := fun h => hxy2 (h ▸ (span_singleton_le_iff_mem w _).mpr hwx)
  have hxline : k ∙ u ⊔ k ∙ w = x.line := by
    rw [← hu]
    exact sup_eq_of_ne x.finrank_pt hw1 x.finrank_line hne1 x.pt_le_line
      ((span_singleton_le_iff_mem w _).mpr hwx)
  have hyline : k ∙ w ⊔ k ∙ v = y.line := by
    rw [← hv]
    exact sup_eq_of_ne hw1 y.finrank_pt y.finrank_line hne2
      ((span_singleton_le_iff_mem w _).mpr hwy) y.pt_le_line
  have hli : LinearIndependent k ![u, w, v] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
    have h2 : c 2 = 0 := by
      by_contra h2
      apply hxy2
      rw [hv, span_singleton_le_iff_mem]
      have hcv : c 2 • v = -(c 0 • u + c 1 • w) := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
        exact hc
      have : c 2 • v ∈ x.line := by
        rw [hcv]
        exact x.line.neg_mem (x.line.add_mem (x.line.smul_mem _ hux) (x.line.smul_mem _ hwx))
      exact (Submodule.smul_mem_iff _ h2).mp this
    rw [h2, zero_smul, add_zero] at hc
    have h1 : c 1 = 0 := by
      by_contra h1
      apply hxy1
      have hcw : c 1 • w = -(c 0 • u) := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
        exact hc
      have hwp : w ∈ x.pt := by
        refine (Submodule.smul_mem_iff _ h1).mp ?_
        rw [hcw, hu]
        exact (k ∙ u).neg_mem ((k ∙ u).smul_mem _ (mem_span_singleton_self u))
      rw [eq_span_singleton_of_mem_of_finrank_eq_one x.finrank_pt hwp hw0,
        span_singleton_le_iff_mem]
      exact hwy
    rw [h1, zero_smul, add_zero] at hc
    have h0 : c 0 = 0 := (smul_eq_zero.mp hc).resolve_right hu0
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  let T := B.equiv (Pi.basisFun k (Fin 3)) (Equiv.refl _)
  have hT : ∀ i : Fin 3, T (![u, w, v] i) = Pi.single i 1 := by
    intro i
    have : B i = ![u, w, v] i := by simp [B]
    rw [← this, Module.Basis.equiv_apply]
    simp
  have hTu : T u = Pi.single 0 1 := hT 0
  have hTw : T w = Pi.single 1 1 := hT 1
  have hTv : T v = Pi.single 2 1 := hT 2
  refine ⟨glOfLinearEquiv T, PlaneFlag.ext ?_ ?_, PlaneFlag.ext ?_ ?_⟩
  · rw [planeGLPerm_pt, hu, map_span_singleton, mulVecLin_glOfLinearEquiv, hTu]
    rfl
  · rw [planeGLPerm_line, ← hxline, Submodule.map_sup, map_span_singleton, map_span_singleton,
      mulVecLin_glOfLinearEquiv, mulVecLin_glOfLinearEquiv, hTu, hTw]
    change _ = span k {Pi.single 0 1, Pi.single 1 1}
    rw [span_insert]
  · rw [planeGLPerm_pt, hv, map_span_singleton, mulVecLin_glOfLinearEquiv, hTv]
    rfl
  · rw [planeGLPerm_line, ← hyline, Submodule.map_sup, map_span_singleton, map_span_singleton,
      mulVecLin_glOfLinearEquiv, mulVecLin_glOfLinearEquiv, hTw, hTv]
    change _ = span k {Pi.single 1 1, Pi.single 2 1}
    rw [span_insert]


namespace ProjPlane


end ProjPlane


namespace ProjPlane


end ProjPlane


namespace ProjPlane


theorem nat_card_ringEquiv_of_card_two (hk : Nat.card k = 2) : Nat.card (k ≃+* k) = 1 := by
  obtain ⟨-, -, -, -, h, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := k) (p := 2) (n := 1) Nat.prime_two le_rfl (by rw [hk]; norm_num)
  exact h

theorem nat_card_ringEquiv_of_card_four (hk : Nat.card k = 4) : Nat.card (k ≃+* k) = 2 := by
  obtain ⟨-, -, -, -, h, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := k) (p := 2) (n := 2) Nat.prime_two (by norm_num) (by rw [hk]; norm_num)
  exact h

theorem nat_card_units_of_card_four (hk : Nat.card k = 4) : Nat.card kˣ = 3 := by
  rw [Nat.card_units, hk]

end ProjPlane

theorem planeOppStab_eq_bot_of_card_two (hk : Nat.card k = 2) : planeOppStab k = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨⟨a, b, σ⟩, rfl, -⟩ := existsUnique_planeDiagPerm_eq hg
  have hu : Nat.card kˣ = 1 := by rw [Nat.card_units, hk]
  have hs : Subsingleton kˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have hσ : Subsingleton (k ≃+* k) :=
    (Nat.card_eq_one_iff_unique.mp (nat_card_ringEquiv_of_card_two hk)).1
  change planeDiagPerm a b σ = 1
  rw [Subsingleton.elim a 1, Subsingleton.elim b 1, Subsingleton.elim σ (RingEquiv.refl k)]
  exact planeDiagPerm_one

theorem nat_card_planeOppStab_of_card_four (hk : Nat.card k = 4) :
    Nat.card (planeOppStab k) = 18 := by
  rw [nat_card_planeOppStab, Nat.card_units, hk, nat_card_ringEquiv_of_card_four hk]


theorem conj_mem_planePairStab {g h : Equiv.Perm (PlaneFlag k)} {x y : PlaneFlag k}
    (hh : h ∈ planeTypeAut k) (hg : g ∈ planePairStab k x y) :
    h * g * h⁻¹ ∈ planePairStab k (h x) (h y) := by
  obtain ⟨hg, hx, hy⟩ := mem_planePairStab.mp hg
  refine mem_planePairStab.mpr ⟨mul_mem (mul_mem hh hg) (inv_mem hh), ?_, ?_⟩
  · simp [Equiv.Perm.mul_apply, hx]
  · simp [Equiv.Perm.mul_apply, hy]

theorem inv_conj_mem_planePairStab {g h : Equiv.Perm (PlaneFlag k)} {x y : PlaneFlag k}
    (hh : h ∈ planeTypeAut k) (hg : g ∈ planePairStab k (h x) (h y)) :
    h⁻¹ * g * h ∈ planePairStab k x y := by
  obtain ⟨hg, hx, hy⟩ := mem_planePairStab.mp hg
  refine mem_planePairStab.mpr ⟨mul_mem (mul_mem (inv_mem hh) hg) hh, ?_, ?_⟩
  · simp [Equiv.Perm.mul_apply, hx]
  · simp [Equiv.Perm.mul_apply, hy]

theorem nat_card_planePairStab_apply {h : Equiv.Perm (PlaneFlag k)} (hh : h ∈ planeTypeAut k)
    (x y : PlaneFlag k) :
    Nat.card (planePairStab k (h x) (h y)) = Nat.card (planePairStab k x y) :=
  Nat.card_congr
    { toFun := fun g => ⟨h⁻¹ * g * h, inv_conj_mem_planePairStab hh g.2⟩
      invFun := fun g => ⟨h * g * h⁻¹, conj_mem_planePairStab hh g.2⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun g => Subtype.ext (by simp [mul_assoc]) }

theorem nat_card_planePairStab_of_isOpposite {x y : PlaneFlag k} (hxy : x.IsOpposite y) :
    Nat.card (planePairStab k x y) = Nat.card (planeOppStab k) := by
  obtain ⟨A, hx, hy⟩ := exists_planeGLPerm_of_isOpposite hxy
  rw [← nat_card_planePairStab_apply (planeGLPerm_mem_planeTypeAut A) x y, hx, hy]

theorem planePairStab_eq_bot_of_card_two (hk : Nat.card k = 2) {x y : PlaneFlag k}
    (hxy : x.IsOpposite y) : planePairStab k x y = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ (by
    rw [nat_card_planePairStab_of_isOpposite hxy, planeOppStab_eq_bot_of_card_two hk,
      Subgroup.card_bot])


theorem eq_one_of_mem_planePairStab_of_forall_panel {x y : PlaneFlag k} (hxy : x.IsOpposite y)
    {g : Equiv.Perm (PlaneFlag k)} (hg : g ∈ planePairStab k x y)
    (h : ∀ z ∈ x.pointPanel ∪ x.linePanel, g z = z) : g = 1 := by
  obtain ⟨A, hx, hy⟩ := exists_planeGLPerm_of_isOpposite hxy
  have hh := planeGLPerm_mem_planeTypeAut A
  have hg' : planeGLPerm A * g * (planeGLPerm A)⁻¹ ∈ planeOppStab k := by
    have := conj_mem_planePairStab hh hg
    rwa [hx, hy] at this
  have key : planeGLPerm A * g * (planeGLPerm A)⁻¹ = 1 := by
    refine eq_one_of_mem_planeOppStab_of_forall_panel hg' fun z hz => ?_
    have hz' : (planeGLPerm A)⁻¹ z ∈ x.pointPanel ∪ x.linePanel := by
      have hinv := mem_planeTypeAut.mp (inv_mem hh) z (planeGLPerm A x)
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at hinv
      rw [← hx] at hz
      rcases hz with hz | hz
      · exact Or.inl (hinv.1.mpr hz)
      · exact Or.inr (hinv.2.mpr hz)
    have := h _ hz'
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, this, Equiv.Perm.inv_def,
      Equiv.apply_symm_apply]
  calc g = (planeGLPerm A)⁻¹ * (planeGLPerm A * g * (planeGLPerm A)⁻¹) * planeGLPerm A := by group
    _ = 1 := by rw [key]; group


end CFSG.Monster.B.Geometry
