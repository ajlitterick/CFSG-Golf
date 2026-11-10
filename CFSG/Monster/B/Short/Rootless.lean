module

public import CFSG.Monster.RootlessLattice
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.RingTheory.Flat.Basic

public section

namespace CFSG.Monster.B.Short

open scoped TensorProduct

variable {L : Type*} [AddCommGroup L]

theorem connected_forall_of_adj {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    {Q : V → Prop} (hQ : ∀ a b, G.Adj a b → Q a → Q b) {a : V} (ha : Q a) (b : V) : Q b := by
  obtain ⟨p⟩ := hG.preconnected a b
  induction p with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hQ _ _ hadj ha)

section Core

variable (h : L →+ L →+ ℤ)

theorem not_two_smul_of_norm_four (hmin : ∀ w, w ≠ 0 → 4 ≤ h w w) {u : L} (hu : h u u = 4)
    (a : L) : u ≠ (2 : ℤ) • a := by
  intro hua
  have ha : h a a = 1 := by
    rw [hua] at hu
    simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_eq_mul] at hu
    linarith
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have := hmin a ha0
  omega

theorem eq_or_eq_neg_of_sub_mem_two (hsymm : ∀ x y, h x y = h y x)
    (hpos : ∀ x, x ≠ 0 → 0 < h x x) (hmin : ∀ w, w ≠ 0 → 4 ≤ h w w)
    {w x : L} (hw : h w w = 4) (hx : h x x = 4) {a : L} (ha : x - w = (2 : ℤ) • a) :
    x = w ∨ x = -w := by
  by_cases ha0 : a = 0
  · left
    rw [ha0, smul_zero, sub_eq_zero] at ha
    exact ha
  · right
    have h16 : h (x - w) (x - w) = 4 * h a a := by
      rw [ha]
      simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_eq_mul]
      ring
    have hpar : h (x + w) (x + w) + h (x - w) (x - w) = 16 := by
      have hxw : h w x = h x w := hsymm w x
      simp only [map_add, map_sub, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, hx, hw, hxw]
      ring
    have hle : h (x + w) (x + w) ≤ 0 := by
      have := hmin a ha0
      linarith
    have h0 : x + w = 0 := by
      by_contra h0
      exact absurd (hpos _ h0) (not_lt.2 hle)
    exact eq_neg_of_add_eq_zero_left h0

variable [Module.IsTorsionFree ℤ L]

theorem eq_id_of_trivial_mod_two (hsymm : ∀ x y, h x y = h y x)
    (hpos : ∀ x, x ≠ 0 → 0 < h x x) (hmin : ∀ w, w ≠ 0 → 4 ≤ h w w) {u : L} (hu : h u u = 4)
    (W : Finset L) (hWne : W.Nonempty) (hW4 : ∀ w ∈ W, h w w = 4) (hWu : ∀ w ∈ W, h u w = 0)
    (hspan : ∀ x : L, h u x = 0 → ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ AddSubgroup.closure (W : Set L))
    (hconn : (SimpleGraph.fromRel fun a b : W => h a b ≠ 0).Connected)
    {y : L} (hy : Odd (h u y)) (g : L →+ L) (hg : ∀ x x', h (g x) (g x') = h x x')
    (hgu : g u = u)
    (htriv : ∀ x : L, Even (h u x) → ∃ m : ℤ, ∃ t : L, g x = x + m • u + (2 : ℤ) • t) :
    ∀ x, g x = x := by
  have hpm : ∀ w ∈ W, g w = w ∨ g w = -w := by
    intro w hw
    obtain ⟨m, t, hmt⟩ := htriv w ⟨0, by rw [hWu w hw]; rfl⟩
    have hgw : h (g w) (g w) = 4 := by rw [hg, hW4 w hw]
    rcases Int.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · refine eq_or_eq_neg_of_sub_mem_two h hsymm hpos hmin (hW4 w hw) hgw (a := t + k • u) ?_
      rw [hmt]
      simp only [smul_add, add_smul, two_smul]
      abel
    · exfalso
      have hwu : w ≠ u := fun e => by
        have := hWu w hw
        rw [e, hu] at this
        exact absurd this (by norm_num)
      have hwu' : w ≠ -u := fun e => by
        have := hWu w hw
        rw [e, map_neg, hu] at this
        exact absurd this (by norm_num)
      have hsums := (rootless_short_sums h hsymm hmin (hW4 w hw) hu hwu hwu').2.1
      have h0 : h w u = 0 := (hsymm w u).trans (hWu w hw)
      rw [h0] at hsums
      have : (0 : ℤ) = 2 ∨ (0 : ℤ) = -2 := hsums.1 ⟨g w, -(t + k • u), by
        rw [hmt]
        simp only [smul_add, smul_neg, add_smul, mul_smul, one_smul, two_smul]
        abel, hgw⟩
      omega
  have hW0 : ∀ w ∈ W, w ≠ 0 := fun w hw e => by
    have := hW4 w hw
    rw [e] at this
    simp at this
  have hadj : ∀ a b : W, (SimpleGraph.fromRel fun a b : W => h a b ≠ 0).Adj a b →
      (g a = a ↔ g b = b) := by
    intro a b hab
    rw [SimpleGraph.fromRel_adj] at hab
    obtain ⟨-, hab⟩ := hab
    have hab' : h a b ≠ 0 := by
      rcases hab with h1 | h1
      · exact h1
      · rwa [hsymm]
    have hiso := hg a b
    have hna : (a : L) ≠ -a := fun e => hW0 a a.2 (by
      have : (2 : ℤ) • (a : L) = 0 := by rw [two_smul]; nth_rw 1 [e]; exact neg_add_cancel _
      exact (smul_eq_zero.1 this).resolve_left (by norm_num))
    have hnb : (b : L) ≠ -b := fun e => hW0 b b.2 (by
      have : (2 : ℤ) • (b : L) = 0 := by rw [two_smul]; nth_rw 1 [e]; exact neg_add_cancel _
      exact (smul_eq_zero.1 this).resolve_left (by norm_num))
    constructor
    · intro ha
      rcases hpm b b.2 with hb | hb
      · exact hb
      · exfalso
        rw [ha, hb, map_neg] at hiso
        exact hab' (by linarith)
    · intro hb
      rcases hpm a a.2 with ha | ha
      · exact ha
      · exfalso
        rw [ha, hb, map_neg, AddMonoidHom.neg_apply] at hiso
        exact hab' (by linarith)
  have hadjn : ∀ a b : W, (SimpleGraph.fromRel fun a b : W => h a b ≠ 0).Adj a b →
      (g a = -a → g b = -b) := by
    intro a b hab ha
    rcases hpm b b.2 with hb | hb
    · exfalso
      have := (hadj a b hab).2 hb
      have hna : (a : L) = -a := this.symm.trans ha
      exact hW0 a a.2 (by
        have : (2 : ℤ) • (a : L) = 0 := by rw [two_smul]; nth_rw 1 [hna]; exact neg_add_cancel _
        exact (smul_eq_zero.1 this).resolve_left (by norm_num))
    · exact hb
  obtain ⟨w₀', hw₀'⟩ := hWne
  let w₀ : W := ⟨w₀', hw₀'⟩
  have hfix_closure : (∀ w ∈ W, g w = w) → ∀ x ∈ AddSubgroup.closure (W : Set L), g x = x := by
    intro hW x hx
    refine AddSubgroup.closure_induction (fun x hx => hW x hx) (map_zero g) (fun x y _ _ hx hy => ?_)
      (fun x _ hx => ?_) hx
    · rw [map_add, hx, hy]
    · rw [map_neg, hx]
  have hneg_closure : (∀ w ∈ W, g w = -w) → ∀ x ∈ AddSubgroup.closure (W : Set L), g x = -x := by
    intro hW x hx
    refine AddSubgroup.closure_induction (fun x hx => hW x hx) (by rw [map_zero, neg_zero])
      (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hx
    · rw [map_add, hx, hy, neg_add]
    · rw [map_neg, hx]
  have hperp : ∀ x : L, h u ((4 : ℤ) • x - h u x • u) = 0 := by
    intro x
    simp only [map_sub, map_zsmul, smul_eq_mul, hu]
    ring
  rcases hpm w₀ w₀.2 with h₀ | h₀
  ·
    have hall : ∀ w ∈ W, g w = w := fun w hw =>
      connected_forall_of_adj hconn (Q := fun b : W => g b = b) (fun a b hab => (hadj a b hab).1) h₀
        ⟨w, hw⟩
    have hperpfix : ∀ x : L, h u x = 0 → g x = x := by
      intro x hx
      obtain ⟨n, hn, hnx⟩ := hspan x hx
      have := hfix_closure hall _ hnx
      rw [map_zsmul] at this
      exact smul_right_injective L hn this
    intro x
    have h1 := hperpfix _ (hperp x)
    rw [map_sub, map_zsmul, map_zsmul, hgu] at h1
    have h2 : (4 : ℤ) • g x = (4 : ℤ) • x := sub_left_injective h1
    exact smul_right_injective L (by norm_num) h2
  ·
    exfalso
    have hall : ∀ w ∈ W, g w = -w := fun w hw =>
      connected_forall_of_adj hconn (Q := fun b : W => g b = -b) (fun a b hab => hadjn a b hab) h₀
        ⟨w, hw⟩
    have hperpneg : ∀ x : L, h u x = 0 → g x = -x := by
      intro x hx
      obtain ⟨n, hn, hnx⟩ := hspan x hx
      have := hneg_closure hall _ hnx
      rw [map_zsmul, ← smul_neg] at this
      exact smul_right_injective L hn this
    have h1 := hperpneg _ (hperp y)
    rw [map_sub, map_zsmul, map_zsmul, hgu] at h1
    obtain ⟨k, hk⟩ := hy
    have e : (4 : ℤ) • g y + (4 : ℤ) • y = (2 : ℤ) • (h u y • u) :=
      calc (4 : ℤ) • g y + (4 : ℤ) • y
          = ((4 : ℤ) • g y - h u y • u) + h u y • u + (4 : ℤ) • y := by abel
        _ = -((4 : ℤ) • y - h u y • u) + h u y • u + (4 : ℤ) • y := by rw [h1]
        _ = (2 : ℤ) • (h u y • u) := by rw [two_smul]; abel
    have h2 : (2 : ℤ) • ((2 : ℤ) • (g y + y)) = (2 : ℤ) • (h u y • u) := by
      rw [← e, smul_smul, smul_add]
      norm_num
    have h3 := smul_right_injective L (by norm_num : (2 : ℤ) ≠ 0) h2
    rw [hk] at h3
    apply not_two_smul_of_norm_four h hmin hu (g y + y - k • u)
    rw [smul_sub, h3, add_smul, one_smul, mul_smul]
    abel

end Core

private theorem zmod_two_cases' : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem modN_two_mk_eq_mk_iff (a b : L) :
    (Submodule.Quotient.mk a : ModN L 2) = Submodule.Quotient.mk b ↔
      ∃ t : L, a - b = (2 : ℤ) • t := by
  rw [Submodule.Quotient.eq]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, ht.symm⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, ht.symm⟩

@[expose] def bModFun (h : L →+ L →+ ℤ) (x y : ModN L 2) : ZMod 2 :=
  Quotient.lift₂ (s₁ := (LinearMap.range (LinearMap.lsmul ℤ L ((2 : ℕ) : ℤ))).quotientRel)
    (s₂ := (LinearMap.range (LinearMap.lsmul ℤ L ((2 : ℕ) : ℤ))).quotientRel)
    (fun a b => ((h a b : ℤ) : ZMod 2)) (by
      intro a₁ b₁ a₂ b₂ ha hb
      obtain ⟨s, hs⟩ := (Submodule.quotientRel_def _).1 ha
      obtain ⟨t, ht⟩ := (Submodule.quotientRel_def _).1 hb
      simp only [LinearMap.lsmul_apply, Nat.cast_ofNat] at hs ht
      have e1 : a₁ = a₂ + (2 : ℤ) • s := by rw [hs]; abel
      have e2 : b₁ = b₂ + (2 : ℤ) • t := by rw [ht]; abel
      have : h a₁ b₁ = h a₂ b₂ + 2 * (h s b₂ + h a₂ t + 2 * h s t) := by
        rw [e1, e2]
        simp only [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply,
          smul_eq_mul]
        ring
      rw [this]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]) x y

theorem bModFun_mk (h : L →+ L →+ ℤ) (a b : L) :
    bModFun h (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = ((h a b : ℤ) : ZMod 2) :=
  rfl

@[expose] def bMod (h : L →+ L →+ ℤ) : ModN L 2 →ₗ[ZMod 2] ModN L 2 →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (bModFun h)
    (fun x x' y => by
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction x' using Submodule.Quotient.induction_on with | H a' => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      rw [← Submodule.Quotient.mk_add, bModFun_mk, bModFun_mk, bModFun_mk, map_add,
        AddMonoidHom.add_apply]
      push_cast
      rfl)
    (fun c x y => by
      rcases zmod_two_cases' c with rfl | rfl
      · induction y using Submodule.Quotient.induction_on with | H b => ?_
        rw [zero_smul, zero_smul, ← Submodule.Quotient.mk_zero, bModFun_mk, map_zero]
        rfl
      · rw [one_smul, one_smul])
    (fun x y y' => by
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      induction y' using Submodule.Quotient.induction_on with | H b' => ?_
      rw [← Submodule.Quotient.mk_add, bModFun_mk, bModFun_mk, bModFun_mk, map_add]
      push_cast
      rfl)
    (fun c x y => by
      rcases zmod_two_cases' c with rfl | rfl
      · induction x using Submodule.Quotient.induction_on with | H a => ?_
        rw [zero_smul, zero_smul, ← Submodule.Quotient.mk_zero, bModFun_mk, map_zero]
        rfl
      · rw [one_smul, one_smul])


@[expose] def vPerp (h : L →+ L →+ ℤ) (u : L) : Submodule (ZMod 2) (ModN L 2) :=
  LinearMap.ker (bMod h (Submodule.Quotient.mk u))

@[expose] def vLine (u : L) : Submodule (ZMod 2) (ModN L 2) :=
  Submodule.span (ZMod 2) {Submodule.Quotient.mk u}

theorem mem_vPerp_mk (h : L →+ L →+ ℤ) (u a : L) :
    (Submodule.Quotient.mk a : ModN L 2) ∈ vPerp h u ↔ ((h u a : ℤ) : ZMod 2) = 0 := Iff.rfl


@[expose] def vLineIn (h : L →+ L →+ ℤ) (u : L) : Submodule (ZMod 2) (vPerp h u) :=
  (vLine u).comap (vPerp h u).subtype

abbrev vQuot (h : L →+ L →+ ℤ) (u : L) : Type _ := vPerp h u ⧸ vLineIn h u

@[expose] def isoGroup (h : L →+ L →+ ℤ) : Subgroup (L ≃ₗ[ℤ] L) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' := fun x y => rfl
  mul_mem' := fun {g g'} hg hg' x y => by
    change h (g (g' x)) (g (g' y)) = h x y
    rw [hg, hg']
  inv_mem' := fun {g} hg x y => by
    have := hg (g⁻¹ x) (g⁻¹ y)
    rw [show g (g⁻¹ x) = x from g.apply_symm_apply x,
      show g (g⁻¹ y) = y from g.apply_symm_apply y] at this
    exact this.symm

@[expose] def isoStab (h : L →+ L →+ ℤ) (u : L) : Subgroup (L ≃ₗ[ℤ] L) where
  carrier := {g | g ∈ isoGroup h ∧ g u = u}
  one_mem' := ⟨one_mem _, rfl⟩
  mul_mem' := fun {g g'} hg hg' => ⟨mul_mem hg.1 hg'.1, by
    change g (g' u) = u
    rw [hg'.2, hg.2]⟩
  inv_mem' := fun {g} hg => ⟨inv_mem hg.1, by
    have := congrArg (g⁻¹ : L ≃ₗ[ℤ] L) hg.2
    rw [show (g⁻¹ : L ≃ₗ[ℤ] L) (g u) = u from g.symm_apply_apply u] at this
    exact this.symm⟩

@[expose] def modTwoMap (g : L →ₗ[ℤ] L) : ModN L 2 →ₗ[ZMod 2] ModN L 2 :=
  AddMonoidHom.toZModLinearMap 2 (Submodule.mapQ _ _ g (by
    rintro _ ⟨w, rfl⟩
    exact ⟨g w, by simp⟩)).toAddMonoidHom

theorem modTwoMap_mk (g : L →ₗ[ℤ] L) (a : L) :
    modTwoMap g (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g a) := rfl

theorem modTwoMap_mem_vPerp (h : L →+ L →+ ℤ) {u : L} {g : L ≃ₗ[ℤ] L} (hg : g ∈ isoStab h u)
    {x : ModN L 2} (hx : x ∈ vPerp h u) : modTwoMap g.toLinearMap x ∈ vPerp h u := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    rw [modTwoMap_mk, mem_vPerp_mk]
    rw [mem_vPerp_mk] at hx
    have := hg.1 u a
    rw [hg.2] at this
    change ((h u (g a) : ℤ) : ZMod 2) = 0
    rw [this, hx]

theorem modTwoMap_mem_vLine {u : L} {g : L ≃ₗ[ℤ] L} (hgu : g u = u) {x : ModN L 2}
    (hx : x ∈ vLine u) : modTwoMap g.toLinearMap x ∈ vLine u := by
  rw [vLine, Submodule.mem_span_singleton] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  refine ⟨a, ?_⟩
  rw [map_smul, modTwoMap_mk]
  change a • Submodule.Quotient.mk u = a • Submodule.Quotient.mk (g u)
  rw [hgu]

@[expose] def stabActFun (h : L →+ L →+ ℤ) (u : L) (g : isoStab h u) :
    Module.End (ZMod 2) (vQuot h u) :=
  Submodule.mapQ (vLineIn h u) (vLineIn h u)
    ((modTwoMap (g : L ≃ₗ[ℤ] L).toLinearMap).restrict fun _ hx => modTwoMap_mem_vPerp h g.2 hx)
    (fun _ hx => modTwoMap_mem_vLine g.2.2 hx)

theorem stabActFun_mk (h : L →+ L →+ ℤ) (u : L) (g : isoStab h u) (x : vPerp h u) :
    stabActFun h u g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨modTwoMap (g : L ≃ₗ[ℤ] L).toLinearMap x,
        modTwoMap_mem_vPerp h g.2 x.2⟩ := rfl

theorem modTwoMap_one (x : ModN L 2) : modTwoMap (LinearMap.id : L →ₗ[ℤ] L) x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H a => rfl

theorem modTwoMap_comp (g g' : L →ₗ[ℤ] L) (x : ModN L 2) :
    modTwoMap (g ∘ₗ g') x = modTwoMap g (modTwoMap g' x) := by
  induction x using Submodule.Quotient.induction_on with
  | H a => rfl

@[expose] def stabAct (h : L →+ L →+ ℤ) (u : L) :
    isoStab h u →* Module.End (ZMod 2) (vQuot h u) where
  toFun := stabActFun h u
  map_one' := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [stabActFun_mk, Module.End.one_apply]
      exact congrArg Submodule.Quotient.mk (Subtype.ext (modTwoMap_one (x : ModN L 2)))
  map_mul' g g' := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [Module.End.mul_apply, stabActFun_mk, stabActFun_mk, stabActFun_mk]
      exact congrArg Submodule.Quotient.mk (Subtype.ext (modTwoMap_comp
        (g : L ≃ₗ[ℤ] L).toLinearMap (g' : L ≃ₗ[ℤ] L).toLinearMap (x : ModN L 2)))


end CFSG.Monster.B.Short
