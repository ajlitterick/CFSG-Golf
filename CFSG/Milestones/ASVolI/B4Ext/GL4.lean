module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.ASVolI

open Module Submodule CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def burnsideB49x_gl_fix (E : Subgroup (W ≃ₗ[ZMod 2] W)) : Submodule (ZMod 2) W where
  carrier := {x | ∀ e ∈ E, e x = x}
  add_mem' {x y} hx hy e he := by rw [map_add, hx e he, hy e he]
  zero_mem' e _ := map_zero e
  smul_mem' a x hx e he := by rw [map_smul, hx e he]

@[expose] def burnsideB49x_gl_comm (E : Subgroup (W ≃ₗ[ZMod 2] W)) : Submodule (ZMod 2) W :=
  Submodule.span (ZMod 2) {y | ∃ e ∈ E, ∃ x, e x - x = y}

@[expose] def burnsideB49x_gl_Q (X : Submodule (ZMod 2) W) : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {g | (∀ x, g x - x ∈ X) ∧ ∀ y ∈ X, g y = y}
  mul_mem' {g h} hg hh := by
    refine ⟨fun x => ?_, fun y hy => ?_⟩
    · rw [LinearEquiv.mul_apply, ← sub_add_sub_cancel (g (h x)) (h x) x]
      exact add_mem (hg.1 (h x)) (hh.1 x)
    · rw [LinearEquiv.mul_apply, hh.2 y hy, hg.2 y hy]
  one_mem' := ⟨fun x => by simp, fun y _ => rfl⟩
  inv_mem' {g} hg := by
    refine ⟨fun x => ?_, fun y hy => ?_⟩
    · rw [LinearEquiv.coe_inv]
      have h := hg.1 (g.symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      rw [← neg_sub]
      exact neg_mem h
    · rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, hg.2 y hy]

theorem burnsideB49x_gl_mem_fix {E : Subgroup (W ≃ₗ[ZMod 2] W)} {x : W} :
    x ∈ burnsideB49x_gl_fix E ↔ ∀ e ∈ E, e x = x :=
  Iff.rfl

theorem burnsideB49x_gl_sub_mem_comm {E : Subgroup (W ≃ₗ[ZMod 2] W)} {e : W ≃ₗ[ZMod 2] W}
    (he : e ∈ E) (x : W) : e x - x ∈ burnsideB49x_gl_comm E :=
  Submodule.subset_span ⟨e, he, x, rfl⟩

theorem burnsideB49x_gl_mem_Q {X : Submodule (ZMod 2) W} {g : W ≃ₗ[ZMod 2] W} :
    g ∈ burnsideB49x_gl_Q X ↔ (∀ x, g x - x ∈ X) ∧ ∀ y ∈ X, g y = y :=
  Iff.rfl


theorem burnsideB49x_gl_apply_apply {e : W ≃ₗ[ZMod 2] W} (h : e * e = 1) (x : W) :
    e (e x) = x := by
  rw [← LinearEquiv.mul_apply, h]
  rfl

theorem burnsideB49x_gl_apply_comm {e e' : W ≃ₗ[ZMod 2] W} (h : e * e' = e' * e) (x : W) :
    e (e' x) = e' (e x) := by
  rw [← LinearEquiv.mul_apply, h, LinearEquiv.mul_apply]

theorem burnsideB49x_gl_apply_sub {e : W ≃ₗ[ZMod 2] W} (h : e * e = 1) (x : W) :
    e (e x - x) = e x - x := by
  rw [map_sub, burnsideB49x_gl_apply_apply h, two_sub, two_sub, add_comm]

theorem burnsideB49x_gl_finrank_lt [FiniteDimensional (ZMod 2) W] {S T : Submodule (ZMod 2) W}
    (hST : S ≤ T) {x : W} (hxT : x ∈ T) (hxS : x ∉ S) :
    finrank (ZMod 2) S < finrank (ZMod 2) T :=
  Submodule.finrank_lt_finrank_of_lt (SetLike.lt_iff_le_and_exists.2 ⟨hST, x, hxT, hxS⟩)

theorem burnsideB49x_gl_mem_or_add_mem [FiniteDimensional (ZMod 2) W]
    {D : Submodule (ZMod 2) W} {x : W} (hx : x ∉ D)
    (hD : finrank (ZMod 2) W ≤ finrank (ZMod 2) D + 1) (w : W) : w ∈ D ∨ w + x ∈ D := by
  have h1 := burnsideB49x_gl_finrank_lt (le_sup_left : D ≤ D ⊔ (ZMod 2) ∙ x)
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)) hx
  have htop : D ⊔ (ZMod 2) ∙ x = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by omega))
  have hw : w ∈ D ⊔ (ZMod 2) ∙ x := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨d, hd, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
  rcases mem_span_singleton_iff_two.1 hz with rfl | rfl
  · left
    rwa [add_zero]
  · right
    rwa [add_assoc, two_add_self, add_zero]

theorem burnsideB49x_gl_quad_of_codim [FiniteDimensional (ZMod 2) W]
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (h2 : ∀ e ∈ E, e * e = 1)
    (hdim : finrank (ZMod 2) W ≤ finrank (ZMod 2) (burnsideB49x_gl_fix E) + 2) :
    burnsideB49x_gl_comm E ≤ burnsideB49x_gl_fix E := by
  rw [burnsideB49x_gl_comm, Submodule.span_le]
  rintro _ ⟨e, he, x, rfl⟩
  by_contra hy
  change e x - x ∉ burnsideB49x_gl_fix E at hy
  have hey : e (e x - x) = e x - x := burnsideB49x_gl_apply_sub (h2 e he) x
  set y := e x - x with hy_def
  set D := burnsideB49x_gl_fix E ⊔ (ZMod 2) ∙ y with hD_def
  have hDe : ∀ d ∈ D, e d = d := by
    intro d hd
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hd
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [map_add, map_smul, ha e he, hey]
  have hD : finrank (ZMod 2) (burnsideB49x_gl_fix E) < finrank (ZMod 2) D :=
    burnsideB49x_gl_finrank_lt le_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)) hy
  have hxD : x ∉ D := by
    intro hx
    apply hy
    rw [hy_def, hDe x hx, sub_self]
    exact zero_mem _
  have hw : ∀ w, e w - w = 0 ∨ e w - w = y := by
    intro w
    rcases burnsideB49x_gl_mem_or_add_mem hxD (by omega) w with hwD | hwD
    · left
      rw [hDe w hwD, sub_self]
    · right
      have h := hDe _ hwD
      rw [map_add] at h
      rw [hy_def, two_sub, two_sub]
      calc e w + w = e w + w + (e x + x) + (e x + x) := by
            rw [add_assoc (e w + w), two_add_self, add_zero]
        _ = (e w + e x) + (w + x) + (e x + x) := by abel
        _ = e x + x := by rw [h, two_add_self, zero_add]
  apply hy
  intro e' he'
  have hz : e' y - y = e (e' x - x) - (e' x - x) := by
    rw [hy_def, map_sub, ← burnsideB49x_gl_apply_comm (hc e he e' he'), map_sub]
    abel
  rcases hw (e' x - x) with h0 | h1
  · rw [← hz, sub_eq_zero] at h0
    exact h0
  · exfalso
    rw [← hz, sub_eq_iff_eq_add, two_add_self] at h1
    have hy0 : y = 0 := e'.injective (by rw [h1, map_zero])
    exact hy (hy0 ▸ zero_mem _)


@[expose] def burnsideB49x_gl_hom (C B : Submodule (ZMod 2) W) (g : W ≃ₗ[ZMod 2] W)
    (hC : ∀ x ∈ C, g x = x) (hB : ∀ x, g x - x ∈ B) : (W ⧸ C) →ₗ[ZMod 2] B :=
  C.liftQ (LinearMap.codRestrict B ((g : W →ₗ[ZMod 2] W) - LinearMap.id) hB) fun x hx => by
    rw [LinearMap.mem_ker]
    ext
    simp [hC x hx]

theorem burnsideB49x_gl_hom_mk (C B : Submodule (ZMod 2) W) (g : W ≃ₗ[ZMod 2] W)
    (hC : ∀ x ∈ C, g x = x) (hB : ∀ x, g x - x ∈ B) (x : W) :
    ((burnsideB49x_gl_hom C B g hC hB (Submodule.Quotient.mk x) : B) : W) = g x - x :=
  rfl

theorem burnsideB49x_gl_hom_inj {C B : Submodule (ZMod 2) W} {g g' : W ≃ₗ[ZMod 2] W}
    {hC : ∀ x ∈ C, g x = x} {hB : ∀ x, g x - x ∈ B} {hC' : ∀ x ∈ C, g' x = x}
    {hB' : ∀ x, g' x - x ∈ B}
    (h : burnsideB49x_gl_hom C B g hC hB = burnsideB49x_gl_hom C B g' hC' hB') : g = g' := by
  ext x
  have hx := congrArg (fun φ : (W ⧸ C) →ₗ[ZMod 2] B => ((φ (Submodule.Quotient.mk x) : B) : W)) h
  simp only [burnsideB49x_gl_hom_mk] at hx
  exact sub_left_injective hx

theorem burnsideB49x_gl_card_hom [FiniteDimensional (ZMod 2) W] (C B : Submodule (ZMod 2) W) :
    Nat.card ((W ⧸ C) →ₗ[ZMod 2] B) =
      2 ^ ((finrank (ZMod 2) W - finrank (ZMod 2) C) * finrank (ZMod 2) B) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Module.finrank_linearMap,
    Submodule.finrank_quotient]

theorem burnsideB49x_gl_card_le [FiniteDimensional (ZMod 2) W] {ι : Type*}
    (f : ι → (W ≃ₗ[ZMod 2] W)) (hf : Function.Injective f) (C B : Submodule (ZMod 2) W)
    (hC : ∀ i, ∀ x ∈ C, f i x = x) (hB : ∀ i x, f i x - x ∈ B) :
    Nat.card ι ≤ 2 ^ ((finrank (ZMod 2) W - finrank (ZMod 2) C) * finrank (ZMod 2) B) := by
  haveI : Finite ((W ⧸ C) →ₗ[ZMod 2] B) := Module.finite_of_finite (ZMod 2)
  rw [← burnsideB49x_gl_card_hom C B]
  exact Nat.card_le_card_of_injective (fun i => burnsideB49x_gl_hom C B (f i) (hC i) (hB i))
    fun i j hij => hf (burnsideB49x_gl_hom_inj hij)

theorem burnsideB49x_gl_card_le_fix_comm [FiniteDimensional (ZMod 2) W]
    (E : Subgroup (W ≃ₗ[ZMod 2] W)) :
    Nat.card E ≤ 2 ^ ((finrank (ZMod 2) W - finrank (ZMod 2) (burnsideB49x_gl_fix E)) *
      finrank (ZMod 2) (burnsideB49x_gl_comm E)) :=
  burnsideB49x_gl_card_le (fun e : E => (e : W ≃ₗ[ZMod 2] W)) Subtype.val_injective _ _
    (fun e _ hx => hx e e.2) (fun e x => burnsideB49x_gl_sub_mem_comm e.2 x)

theorem burnsideB49x_gl_one_le_finrank_fix [FiniteDimensional (ZMod 2) W]
    (hW : 0 < finrank (ZMod 2) W) {E : Subgroup (W ≃ₗ[ZMod 2] W)} (h2 : ∀ e ∈ E, e * e = 1) :
    1 ≤ finrank (ZMod 2) (burnsideB49x_gl_fix E) := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  have hp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, sq]
    exact h2 _ g.2)⟩
  have hdvd : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 hW.ne'
  obtain ⟨b, hb, hb0⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hdvd
    (a := 0) (MulAction.mem_fixedPoints.2 fun g => show (g : W ≃ₗ[ZMod 2] W) 0 = 0 from map_zero _)
  have hbfix : b ∈ burnsideB49x_gl_fix E := fun e he => MulAction.mem_fixedPoints.1 hb ⟨e, he⟩
  rw [Submodule.one_le_finrank_iff]
  intro hbot
  rw [hbot, Submodule.mem_bot] at hbfix
  exact hb0 hbfix.symm

theorem burnsideB49x_gl_Q_quad {X : Submodule (ZMod 2) W} {g g' : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ burnsideB49x_gl_Q X) (hg' : g' ∈ burnsideB49x_gl_Q X) (x : W) :
    g (g' x - x) = g' x - x :=
  hg.2 _ (hg'.1 x)

theorem burnsideB49x_gl_Q_apply_apply {X : Submodule (ZMod 2) W} {g g' : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ burnsideB49x_gl_Q X) (hg' : g' ∈ burnsideB49x_gl_Q X) (x : W) :
    g (g' x) = g x + (g' x - x) := by
  have h : g' x = x + (g' x - x) := by abel
  calc g (g' x) = g (x + (g' x - x)) := congrArg g h
    _ = g x + (g' x - x) := by rw [map_add, burnsideB49x_gl_Q_quad hg hg' x]


theorem burnsideB49x_gl_Q_mul_self {X : Submodule (ZMod 2) W} {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ burnsideB49x_gl_Q X) : g * g = 1 := by
  ext x
  rw [LinearEquiv.mul_apply, burnsideB49x_gl_Q_apply_apply hg hg, two_sub, ← add_assoc,
    two_add_self, zero_add]
  rfl

@[expose] def burnsideB49x_gl_ofHom (X : Submodule (ZMod 2) W) (φ : (W ⧸ X) →ₗ[ZMod 2] X) :
    W ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofInvolutive (LinearMap.id + X.subtype ∘ₗ φ ∘ₗ X.mkQ) fun x => by
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.subtype_apply]
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero X).2 (φ _).2, add_zero,
      add_assoc, two_add_self, add_zero]

theorem burnsideB49x_gl_ofHom_apply (X : Submodule (ZMod 2) W) (φ : (W ⧸ X) →ₗ[ZMod 2] X)
    (x : W) : burnsideB49x_gl_ofHom X φ x = x + (φ (Submodule.Quotient.mk x) : W) :=
  rfl

theorem burnsideB49x_gl_ofHom_mem (X : Submodule (ZMod 2) W) (φ : (W ⧸ X) →ₗ[ZMod 2] X) :
    burnsideB49x_gl_ofHom X φ ∈ burnsideB49x_gl_Q X := by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · rw [burnsideB49x_gl_ofHom_apply, add_sub_cancel_left]
    exact (φ _).2
  · rw [burnsideB49x_gl_ofHom_apply, (Submodule.Quotient.mk_eq_zero X).2 hy, map_zero,
      Submodule.coe_zero, add_zero]

theorem burnsideB49x_gl_card_Q_eq [FiniteDimensional (ZMod 2) W] (X : Submodule (ZMod 2) W) :
    Nat.card (burnsideB49x_gl_Q X) =
      2 ^ ((finrank (ZMod 2) W - finrank (ZMod 2) X) * finrank (ZMod 2) X) := by
  rw [← burnsideB49x_gl_card_hom X X]
  refine Nat.card_eq_of_bijective
    (fun g : burnsideB49x_gl_Q X => burnsideB49x_gl_hom X X g g.2.2 g.2.1) ⟨fun g g' h =>
      Subtype.ext (burnsideB49x_gl_hom_inj h), fun φ => ⟨⟨_, burnsideB49x_gl_ofHom_mem X φ⟩, ?_⟩⟩
  refine LinearMap.ext fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    apply Subtype.ext
    change burnsideB49x_gl_ofHom X φ x - x = _
    rw [burnsideB49x_gl_ofHom_apply, add_sub_cancel_left]

theorem burnsideB49x_gl_card_Q [FiniteDimensional (ZMod 2) W] {X : Submodule (ZMod 2) W}
    {k n : ℕ} (hk : finrank (ZMod 2) X = k) (hn : finrank (ZMod 2) W = n) :
    Nat.card (burnsideB49x_gl_Q X) = 2 ^ (k * (n - k)) := by
  rw [burnsideB49x_gl_card_Q_eq, hk, hn, mul_comm]

theorem burnsideB49x_gl_three [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 3)
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (h2 : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 4 := by
  have hc1 := burnsideB49x_gl_one_le_finrank_fix (by omega) h2
  have hbc := Submodule.finrank_mono (burnsideB49x_gl_quad_of_codim hc h2 (by omega))
  have hc3 := Submodule.finrank_le (burnsideB49x_gl_fix E)
  have hcard := burnsideB49x_gl_card_le_fix_comm E
  rw [hW] at hcard hc3
  have hexp : (3 - finrank (ZMod 2) (burnsideB49x_gl_fix E)) *
      finrank (ZMod 2) (burnsideB49x_gl_comm E) ≤ 2 := by
    generalize finrank (ZMod 2) (burnsideB49x_gl_fix E) = c at hc1 hbc hc3 ⊢
    generalize finrank (ZMod 2) (burnsideB49x_gl_comm E) = b at hbc ⊢
    interval_cases c <;> omega
  calc Nat.card E ≤ 2 ^ ((3 - finrank (ZMod 2) (burnsideB49x_gl_fix E)) *
        finrank (ZMod 2) (burnsideB49x_gl_comm E)) := hcard
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hexp
    _ = 4 := by norm_num


end CFSG.ASVolI
