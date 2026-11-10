module

public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.SeitzReduction

namespace ClassicalLagrangian

open Matrix

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {β : LinearMap.BilinForm K V}
  {f : Module.End K V}

theorem transvection_apply (β : LinearMap.BilinForm K V) (u x : V) :
    LinearMap.transvection (β.flip u) u x = x + β x u • u :=
  rfl

theorem transvection_mul_apply (β : LinearMap.BilinForm K V) (u v x : V) :
    (LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v) x =
      x + β x v • v + (β x u + β x v * β v u) • u := by
  rw [Module.End.mul_apply, transvection_apply, transvection_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

theorem exists_apply_eq_smul_of_commute_transvection {u : V}
    (hf : Commute f (LinearMap.transvection (β.flip u) u)) {x : V} (hx : β x u ≠ 0) :
    ∃ a : K, f u = a • u := by
  have h : f (LinearMap.transvection (β.flip u) u x) =
      LinearMap.transvection (β.flip u) u (f x) := LinearMap.congr_fun hf.eq x
  rw [transvection_apply, transvection_apply, map_add, map_smul, add_right_inj] at h
  refine ⟨(β x u)⁻¹ * β (f x) u, ?_⟩
  rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hx, one_smul]


theorem apply_eq_of_commute_transvection_mul {u v : V}
    (hf : Commute f (LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v))
    {x : V} (hxv : β x v = 0) (hxu : β x u = 1) :
    f u = (β (f x) u + β (f x) v * β v u) • u + β (f x) v • v := by
  have h : f ((LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v) x) =
      (LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v) (f x) :=
    LinearMap.congr_fun hf.eq x
  rw [transvection_mul_apply, transvection_mul_apply, hxv, hxu] at h
  simp only [zero_smul, add_zero, zero_mul, one_smul, map_add] at h
  rw [add_assoc, add_right_inj] at h
  rw [h, add_comm]

theorem apply_eq_zero_of_commute_transvection_mul {u v : V}
    (hf : Commute f (LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v))
    (huv : LinearIndependent K ![u, v]) {x : V} (hxu : β x u = 0) (hxv : β x v = 0) :
    β (f x) u = 0 ∧ β (f x) v = 0 := by
  have h : f ((LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v) x) =
      (LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v) (f x) :=
    LinearMap.congr_fun hf.eq x
  rw [transvection_mul_apply, transvection_mul_apply, hxv, hxu] at h
  simp only [zero_smul, add_zero, zero_mul] at h
  rw [add_assoc, left_eq_add] at h
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp huv
    (β (f x) u + β (f x) v * β v u) (β (f x) v) (by rw [add_comm]; exact h)
  rw [h2, zero_mul, add_zero] at h1
  exact ⟨h1, h2⟩

theorem exists_forall_apply_eq_smul {H : Submodule K V}
    (h : ∀ x ∈ H, ∃ a : K, f x = a • x) : ∃ c : K, ∀ x ∈ H, f x = c • x := by
  have hfH : ∀ x ∈ H, f x ∈ H := fun x hx => by
    obtain ⟨a, ha⟩ := h x hx
    rw [ha]
    exact H.smul_mem a hx
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := f.restrict hfH) (fun y => by
      obtain ⟨a, ha⟩ := h y y.2
      rw [LinearIndependent.pair_iff]
      intro hli
      have := hli a (-1) (by
        apply Subtype.ext
        simp [LinearMap.restrict_apply, ha])
      exact one_ne_zero (neg_eq_zero.mp this.2))
  refine ⟨c, fun x hx => ?_⟩
  have := congrArg Subtype.val (LinearMap.congr_fun hc ⟨x, hx⟩)
  simpa [LinearMap.restrict_apply] using this

theorem exists_ne_zero_orthogonal_pair [FiniteDimensional K V] (β : LinearMap.BilinForm K V)
    {H : Submodule K V} (hdim : 2 < Module.finrank K H) (x v : V) :
    ∃ z ∈ H, z ≠ 0 ∧ β z x = 0 ∧ β z v = 0 := by
  let φ : H →ₗ[K] K × K := LinearMap.prod ((β.flip x).domRestrict H) ((β.flip v).domRestrict H)
  have hker : LinearMap.ker φ ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank K (LinearMap.range φ) ≤ 2 := by
      have := Submodule.finrank_le (LinearMap.range φ)
      simpa [Module.finrank_prod] using this
    rw [hbot, finrank_bot] at h1
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hz' := LinearMap.mem_ker.mp hz
  refine ⟨z, z.2, fun h => hz0 (Subtype.ext h), ?_, ?_⟩
  · simpa [φ] using congrArg Prod.fst hz'
  · simpa [φ] using congrArg Prod.snd hz'

theorem exists_forall_apply_eq_smul_of_commute_transvection_mul [FiniteDimensional K V]
    {H : Submodule K V} (halt : ∀ x ∈ H, β x x = 0)
    (hnd : ∀ x ∈ H, x ≠ 0 → ∃ y ∈ H, β x y ≠ 0) (hdim : 2 < Module.finrank K H)
    (hf : ∀ u ∈ H, ∀ v ∈ H, β u v = 1 →
      Commute f (LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v)) :
    ∃ c : K, ∀ x ∈ H, f x = c • x := by
  have hskew : ∀ a ∈ H, ∀ b ∈ H, β b a = -β a b := by
    intro a ha b hb
    have := halt (a + b) (H.add_mem ha hb)
    simp only [map_add, LinearMap.add_apply, halt a ha, halt b hb, zero_add, add_zero] at this
    linear_combination this
  apply exists_forall_apply_eq_smul
  intro x hx
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [hx0, map_zero, smul_zero]⟩
  obtain ⟨y, hy, hxy⟩ := hnd x hx hx0
  have hvH : (β x y)⁻¹ • y ∈ H := H.smul_mem _ hy
  have hxv : β x ((β x y)⁻¹ • y) = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hxy]
  set v := (β x y)⁻¹ • y with hv
  have key : ∀ w ∈ H, β x w = 1 → ∃ a b : K, f x = a • x + b • w := by
    intro w hw hxw
    refine ⟨_, _, apply_eq_of_commute_transvection_mul (hf x hx w hw hxw) (x := -w) ?_ ?_⟩
    · rw [map_neg, LinearMap.neg_apply, halt w hw, neg_zero]
    · rw [map_neg, LinearMap.neg_apply, hskew x hx w hw, hxw, neg_neg]
  obtain ⟨z, hzH, hz0, hzx, hzv⟩ := exists_ne_zero_orthogonal_pair β hdim x v
  have hxz : β x z = 0 := by rw [hskew z hzH x hx, hzx, neg_zero]
  have hxw : β x (v + z) = 1 := by rw [map_add, hxv, hxz, add_zero]
  obtain ⟨a, b, hab⟩ := key v hvH hxv
  obtain ⟨a', b', hab'⟩ := key (v + z) (H.add_mem hvH hzH) hxw
  have hE : a • x + b • v = a' • x + b' • (v + z) := hab.symm.trans hab'
  have hvx : β v x = -1 := by rw [hskew x hx v hvH, hxv]
  have e1 := congrArg (fun t => β t x) hE
  have e2 := congrArg (fun t => β t v) hE
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    halt x hx, halt v hvH, hvx, hzx, hzv, hxv] at e1 e2
  have hbb : b = b' := by linear_combination -e1
  have haa : a = a' := by linear_combination e2
  subst hbb haa
  have hbz : b • z = 0 := by
    rw [smul_add, ← add_assoc, left_eq_add] at hE
    exact hE
  rcases smul_eq_zero.mp hbz with hb | hz
  · exact ⟨a, by rw [hab, hb, zero_smul, add_zero]⟩
  · exact absurd hz hz0

theorem exists_eq_smul_one_of_commute_transvection (hβ : ∀ u, u ≠ 0 → ∃ x, β x u ≠ 0)
    (hf : ∀ u, Commute f (LinearMap.transvection (β.flip u) u)) : ∃ c : K, f = c • 1 := by
  obtain ⟨c, hc⟩ := exists_forall_apply_eq_smul (H := ⊤) (f := f) (fun u _ => by
    by_cases hu : u = 0
    · exact ⟨0, by rw [hu, map_zero, smul_zero]⟩
    obtain ⟨x, hx⟩ := hβ u hu
    exact exists_apply_eq_smul_of_commute_transvection (hf u) hx)
  exact ⟨c, LinearMap.ext fun x => by simp [hc x Submodule.mem_top]⟩

theorem exists_eq_smul_one_of_commute_transvection_mul [FiniteDimensional K V] (halt : β.IsAlt)
    (hβ : ∀ x, x ≠ 0 → ∃ y, β x y ≠ 0) (hdim : 2 < Module.finrank K V)
    (hf : ∀ u v, β u v = 1 →
      Commute f (LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v)) :
    ∃ c : K, f = c • 1 := by
  obtain ⟨c, hc⟩ := exists_forall_apply_eq_smul_of_commute_transvection_mul (H := ⊤)
    (fun x _ => halt.self_eq_zero x)
    (fun x _ hx => let ⟨y, hy⟩ := hβ x hx; ⟨y, Submodule.mem_top, hy⟩)
    (by rwa [finrank_top]) (fun u _ v _ huv => hf u v huv)
  exact ⟨c, LinearMap.ext fun x => by simp [hc x Submodule.mem_top]⟩


theorem transvection_isometry_of_self {u : V} (hu : β u u = 0) (hskew : ∀ y, β u y = -β y u)
    (x y : V) :
    β (LinearMap.transvection (β.flip u) u x) (LinearMap.transvection (β.flip u) u y) =
      β x y := by
  rw [transvection_apply, transvection_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu,
    hskew y]
  ring

theorem transvection_isometry (halt : β.IsAlt) (u x y : V) :
    β (LinearMap.transvection (β.flip u) u x) (LinearMap.transvection (β.flip u) u y) =
      β x y :=
  transvection_isometry_of_self (halt.self_eq_zero u) (fun y => (halt.neg_eq y u).symm) x y

theorem transvection_mul_self [CharP K 2] {u : V} (hu : β u u = 0) :
    LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip u) u = 1 := by
  ext x
  rw [transvection_mul_apply, hu, mul_zero, add_zero, Module.End.one_apply, add_assoc,
    ← two_smul K, CharTwo.two_eq_zero, zero_smul, add_zero]

theorem transvection_mul_transvection_pow_three_of_self [CharP K 2] {u v : V} (hu : β u u = 0)
    (hv : β v v = 0) (huv : β u v = 1) (hvu : β v u = 1) :
    (LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v) ^ 3 = 1 := by
  set g := LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v with hgdef
  have hg : ∀ x, g x = x + (β x u + β x v) • u + β x v • v := by
    intro x
    rw [hgdef, transvection_mul_apply, hvu, mul_one]
    abel
  clear_value g
  have hgu : ∀ x, β (g x) u = β x u + β x v := by
    intro x
    rw [hg]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu, hvu]
    ring
  have hgv : ∀ x, β (g x) v = β x u := by
    intro x
    rw [hg]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hv, huv]
    linear_combination (β x v) * (CharTwo.two_eq_zero : (2 : K) = 0)
  ext x
  rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply]
  set a := β x u
  set b := β x v
  have h1 : g x = x + (a + b) • u + b • v := hg x
  have h1u : β (g x) u = a + b := hgu x
  have h1v : β (g x) v = a := hgv x
  have h2 : g (g x) = x + (a + b) • u + b • v + ((a + b) + a) • u + a • v := by
    rw [hg (g x), h1u, h1v, h1]
  have h2u : β (g (g x)) u = (a + b) + a := by rw [hgu, h1u, h1v]
  have h2v : β (g (g x)) v = a + b := by rw [hgv, h1u]
  rw [hg (g (g x)), h2u, h2v, h2]
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  calc x + (a + b) • u + b • v + ((a + b) + a) • u + a • v + (((a + b) + a) + (a + b)) • u +
        (a + b) • v = x + (2 * (3 * a + 2 * b)) • u + (2 * (a + b)) • v := by module
    _ = x := by rw [h2K, zero_mul, zero_mul, zero_smul, zero_smul, add_zero, add_zero]

theorem transvection_mul_transvection_pow_three [CharP K 2] (halt : β.IsAlt) {u v : V}
    (huv : β u v = 1) :
    (LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v) ^ 3 = 1 :=
  transvection_mul_transvection_pow_three_of_self (halt.self_eq_zero u) (halt.self_eq_zero v)
    huv (by rw [← halt.neg_eq u v, huv, CharTwo.neg_eq])

theorem apply_eq_smul_self_of_forall_orthogonal (hsymm : ∀ x y, β x y = β y x)
    (hsep : ∀ x, (∀ y, β x y = 0) → x = 0) {d : V} (hdd : β d d = 1)
    (hd : ∀ u, β d u = 0 → β (f d) u = 0) : f d = β d (f d) • d := by
  rw [← sub_eq_zero]
  apply hsep
  intro z
  have h1 := hd (z - β d z • d) (by rw [map_sub, map_smul, smul_eq_mul, hdd, mul_one, sub_self])
  have h2 : β (f d) d = β d (f d) := hsymm _ _
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h1 ⊢
  rw [h2] at h1
  linear_combination h1

theorem apply_eq_smul_of_commute_shear {d h : V} (hdd : β d d = 1) (hh : β d h = 0) {μ : K}
    (hfd : f d = μ • d) (hτ : Commute f ((β.flip d).smulRight h + (β.flip h).smulRight d)) :
    f h = μ • h := by
  have hτd : ((β.flip d).smulRight h + (β.flip h).smulRight d) d = h := by
    simp [LinearMap.smulRight_apply, hdd, hh]
  have e : f (((β.flip d).smulRight h + (β.flip h).smulRight d) d) =
      ((β.flip d).smulRight h + (β.flip h).smulRight d) (f d) := LinearMap.congr_fun hτ.eq d
  rwa [hτd, hfd, map_smul, hτd] at e

theorem eq_smul_one_of_apply_eq_smul_of_commute_shear (hsymm : ∀ x y, β x y = β y x)
    (hsep : ∀ x, (∀ y, β x y = 0) → x = 0) {d : V} (hdd : β d d = 1) {c : K}
    (hH : ∀ x, β d x = 0 → f x = c • x) (hd : ∀ u, β d u = 0 → β (f d) u = 0)
    {h : V} (hh : β d h = 0) (hh0 : h ≠ 0)
    (hτ : Commute f ((β.flip d).smulRight h + (β.flip h).smulRight d)) : f = c • 1 := by
  have hproj : ∀ x, β d (x - β d x • d) = 0 := fun x => by
    rw [map_sub, map_smul, smul_eq_mul, hdd, mul_one, sub_self]
  have hfd := apply_eq_smul_self_of_forall_orthogonal hsymm hsep hdd hd
  have hc : c = β d (f d) :=
    smul_left_injective K hh0 ((hH h hh).symm.trans (apply_eq_smul_of_commute_shear hdd hh hfd hτ))
  ext x
  rw [LinearMap.smul_apply, Module.End.one_apply]
  have hx : x = (x - β d x • d) + β d x • d := by abel
  conv_lhs => rw [hx]
  rw [map_add, map_smul, hH _ (hproj x), hfd, ← hc, smul_comm (β d x) c d, ← smul_add, ← hx]

theorem exists_ne_zero_of_mem_ker (hsymm : ∀ x y, β x y = β y x)
    (hsep : ∀ x, (∀ y, β x y = 0) → x = 0) {d : V} (hdd : β d d = 1) {x : V} (hx : β d x = 0)
    (hx0 : x ≠ 0) : ∃ y, β d y = 0 ∧ β x y ≠ 0 := by
  have : ∃ y, β x y ≠ 0 := by
    by_contra hcon
    exact hx0 (hsep x fun y => not_not.mp fun hy => hcon ⟨y, hy⟩)
  obtain ⟨y, hy⟩ := this
  refine ⟨y - β d y • d, by rw [map_sub, map_smul, smul_eq_mul, hdd, mul_one, sub_self], ?_⟩
  rwa [map_sub, map_smul, smul_eq_mul, hsymm x d, hx, mul_zero, sub_zero]


theorem apply_eq_zero_of_commute_transvection_mul_of_mem_ker (hsymm : ∀ x y, β x y = β y x)
    (hsep : ∀ x, (∀ y, β x y = 0) → x = 0) {d : V} (hdd : β d d = 1)
    (halt : ∀ x, β d x = 0 → β x x = 0)
    (hg : ∀ u v, β d u = 0 → β d v = 0 → β u v = 1 →
      Commute f (LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v))
    {u : V} (hu : β d u = 0) : β (f d) u = 0 := by
  by_cases hu0 : u = 0
  · rw [hu0, map_zero]
  obtain ⟨y, hy, hxy⟩ := exists_ne_zero_of_mem_ker hsymm hsep hdd hu hu0
  have hv : β d ((β u y)⁻¹ • y) = 0 := by rw [map_smul, hy, smul_zero]
  have huv : β u ((β u y)⁻¹ • y) = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hxy]
  have hli : LinearIndependent K ![u, (β u y)⁻¹ • y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e := congrArg (β u) hst
    simp only [map_add, map_smul, smul_eq_mul, halt u hu, huv, map_zero] at e
    have ht : t = 0 := by linear_combination e
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hu0, rfl⟩
  exact (apply_eq_zero_of_commute_transvection_mul (hg u _ hu hv huv) hli hu hv).1

theorem eq_smul_one_of_commute_transvection_mul_of_commute_shear
    (hsymm : ∀ x y, β x y = β y x) (hsep : ∀ x, (∀ y, β x y = 0) → x = 0) {d : V}
    (hdd : β d d = 1) (halt : ∀ x, β d x = 0 → β x x = 0)
    (hg : ∀ u v, β d u = 0 → β d v = 0 → β u v = 1 →
      Commute f (LinearMap.transvection (β.flip u) u * LinearMap.transvection (β.flip v) v))
    {h : V} (hh : β d h = 0) (hh0 : h ≠ 0)
    (hτ : Commute f ((β.flip d).smulRight h + (β.flip h).smulRight d)) : ∃ c : K, f = c • 1 := by
  have hskew : ∀ a b, β d a = 0 → β d b = 0 → β b a = -β a b := by
    intro a b ha hb
    have := halt (a + b) (by rw [map_add, ha, hb, add_zero])
    simp only [map_add, LinearMap.add_apply, halt a ha, halt b hb, zero_add, add_zero] at this
    linear_combination this
  have hd : ∀ u, β d u = 0 → β (f d) u = 0 := fun u hu =>
    apply_eq_zero_of_commute_transvection_mul_of_mem_ker hsymm hsep hdd halt hg hu
  have hfd := apply_eq_smul_self_of_forall_orthogonal hsymm hsep hdd hd
  set μ := β d (f d) with hμ
  clear_value μ
  have hfh : f h = μ • h := apply_eq_smul_of_commute_shear hdd hh hfd hτ
  have hnh : β d (-h) = 0 := by rw [map_neg, hh, neg_zero]
  have key : ∀ u, β d u = 0 → β h u = 1 → f u = μ • u := by
    intro u hu hhu
    have huh : β u (-h) = 1 := by rw [map_neg, hskew h u hh hu, hhu, neg_neg]
    have e := apply_eq_of_commute_transvection_mul (hg u (-h) hu hnh huh) (x := h)
      (by rw [map_neg, halt h hh, neg_zero]) hhu
    rw [hfh] at e
    simp only [map_smul, map_neg, LinearMap.smul_apply, LinearMap.neg_apply, smul_eq_mul, hhu,
      halt h hh] at e
    rw [e]
    module
  obtain ⟨y, hy, hhy⟩ := exists_ne_zero_of_mem_ker hsymm hsep hdd hh hh0
  obtain ⟨u₀, hu₀, hhu₀⟩ : ∃ u₀, β d u₀ = 0 ∧ β h u₀ = 1 :=
    ⟨(β h y)⁻¹ • y, by rw [map_smul, hy, smul_zero],
      by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hhy]⟩
  have hfu₀ := key u₀ hu₀ hhu₀
  have hH : ∀ w, β d w = 0 → f w = μ • w := by
    intro w hw
    obtain ⟨z, hz⟩ : ∃ z, z = w - β h w • u₀ := ⟨_, rfl⟩
    have hzd : β d z = 0 := by rw [hz, map_sub, map_smul, hw, hu₀, smul_zero, sub_zero]
    have hzh : β h z = 0 := by rw [hz, map_sub, map_smul, hhu₀, smul_eq_mul, mul_one, sub_self]
    have h1 := key (u₀ + z) (by rw [map_add, hu₀, hzd, add_zero])
      (by rw [map_add, hhu₀, hzh, add_zero])
    rw [map_add, hfu₀, smul_add, add_right_inj] at h1
    have hw' : w = β h w • u₀ + z := by rw [hz]; abel
    rw [hw', map_add, map_smul, hfu₀, h1, smul_comm (β h w) μ u₀, ← smul_add]
  exact ⟨μ, eq_smul_one_of_apply_eq_smul_of_commute_shear hsymm hsep hdd hH hd hh hh0 hτ⟩

end Abstract

section Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem toLinAlgEquiv'_transvection (J : Matrix ι ι K) (u : ι → K) :
    Matrix.toLinAlgEquiv' (1 + vecMulVec u (J *ᵥ u)) =
      LinearMap.transvection ((Matrix.toBilin' J).flip u) u := by
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLinAlgEquiv'_apply, transvection_apply, Matrix.toBilin'_apply', add_mulVec,
    one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_comm]

theorem toBilin'_one_apply_eq (x y : ι → K) :
    Matrix.toBilin' (1 : Matrix ι ι K) x y = x ⬝ᵥ y := by
  rw [Matrix.toBilin'_apply', one_mulVec]

theorem toLinAlgEquiv'_shear (d h : ι → K) :
    Matrix.toLinAlgEquiv' (vecMulVec h d + vecMulVec d h) =
      ((Matrix.toBilin' (1 : Matrix ι ι K)).flip d).smulRight h +
        ((Matrix.toBilin' (1 : Matrix ι ι K)).flip h).smulRight d := by
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLinAlgEquiv'_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smulRight_apply]
  change _ = Matrix.toBilin' 1 x d • h + Matrix.toBilin' 1 x h • d
  rw [toBilin'_one_apply_eq, toBilin'_one_apply_eq, add_mulVec, vecMulVec_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul, dotProduct_comm d, dotProduct_comm h]

theorem eq_smul_one_of_toLinAlgEquiv' {M : Matrix ι ι K} {c : K}
    (h : Matrix.toLinAlgEquiv' M = c • 1) : M = c • 1 := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [h, map_smul, map_one]

theorem commute_toLinAlgEquiv' {M X : Matrix ι ι K} (h : Commute M X) :
    Commute (Matrix.toLinAlgEquiv' M) (Matrix.toLinAlgEquiv' X) :=
  h.map _

theorem toLinAlgEquiv'_transvection_one (u : ι → K) :
    Matrix.toLinAlgEquiv' (1 + vecMulVec u u) =
      LinearMap.transvection ((Matrix.toBilin' (1 : Matrix ι ι K)).flip u) u := by
  have h1 := toLinAlgEquiv'_transvection (1 : Matrix ι ι K) u
  rwa [one_mulVec] at h1

theorem transvectionMatrix_isometry {J : Matrix ι ι K} (halt : ∀ x, x ⬝ᵥ (J *ᵥ x) = 0)
    (u : ι → K) :
    (1 + vecMulVec u (J *ᵥ u))ᵀ * J * (1 + vecMulVec u (J *ᵥ u)) = J := by
  apply Matrix.toBilin'.injective
  rw [← Matrix.toBilin'_comp]
  refine LinearMap.ext₂ fun x y => ?_
  rw [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
  have h := transvection_isometry (β := Matrix.toBilin' J)
    (fun x => by rw [Matrix.toBilin'_apply']; exact halt x) u x y
  rwa [← toLinAlgEquiv'_transvection, Matrix.toLinAlgEquiv'_apply,
    Matrix.toLinAlgEquiv'_apply] at h

theorem transvectionMatrix_mul_pow_three [CharP K 2] {J : Matrix ι ι K}
    (halt : ∀ x, x ⬝ᵥ (J *ᵥ x) = 0) {u v : ι → K} (huv : u ⬝ᵥ (J *ᵥ v) = 1) :
    ((1 + vecMulVec u (J *ᵥ u)) * (1 + vecMulVec v (J *ᵥ v))) ^ 3 = 1 := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_pow, map_mul, map_one, toLinAlgEquiv'_transvection, toLinAlgEquiv'_transvection]
  exact transvection_mul_transvection_pow_three
    (fun x => by rw [Matrix.toBilin'_apply']; exact halt x) (by rwa [Matrix.toBilin'_apply'])

theorem transvectionMatrix_one_mul_self [CharP K 2] {u : ι → K} (hu : u ⬝ᵥ u = 0) :
    (1 + vecMulVec u u) * (1 + vecMulVec u u) = 1 := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_mul, map_one, toLinAlgEquiv'_transvection_one]
  exact transvection_mul_self (by rw [toBilin'_one_apply_eq, hu])

omit [Fintype ι] in
theorem transvectionMatrix_one_transpose (u : ι → K) :
    (1 + vecMulVec u u)ᵀ = 1 + vecMulVec u u := by
  rw [transpose_add, transpose_one, transpose_vecMulVec]

theorem transvectionMatrix_one_mul_pow_three [CharP K 2] {u v : ι → K} (hu : u ⬝ᵥ u = 0)
    (hv : v ⬝ᵥ v = 0) (huv : u ⬝ᵥ v = 1) :
    ((1 + vecMulVec u u) * (1 + vecMulVec v v)) ^ 3 = 1 := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_pow, map_mul, map_one, toLinAlgEquiv'_transvection_one,
    toLinAlgEquiv'_transvection_one]
  exact transvection_mul_transvection_pow_three_of_self (by rwa [toBilin'_one_apply_eq])
    (by rwa [toBilin'_one_apply_eq]) (by rwa [toBilin'_one_apply_eq])
    (by rw [toBilin'_one_apply_eq, dotProduct_comm, huv])

theorem exists_dotProduct_mulVec_ne_zero {J : Matrix ι ι K} (hJ : IsUnit J) {x : ι → K}
    (hx : x ≠ 0) : (∃ y, x ⬝ᵥ (J *ᵥ y) ≠ 0) ∧ ∃ y, y ⬝ᵥ (J *ᵥ x) ≠ 0 := by
  constructor
  · have hxJ : x ᵥ* J ≠ 0 := fun h0 =>
      hx (Matrix.vecMul_injective_iff_isUnit.mpr hJ (by
        show x ᵥ* J = 0 ᵥ* J
        rw [h0, zero_vecMul]))
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxJ
    exact ⟨Pi.single j 1, by rwa [dotProduct_mulVec, dotProduct_single_one]⟩
  · have hJx : J *ᵥ x ≠ 0 := fun h0 =>
      hx (Matrix.mulVec_injective_iff_isUnit.mpr hJ (by rw [h0, mulVec_zero]))
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hJx
    exact ⟨Pi.single j 1, by rwa [single_one_dotProduct]⟩


theorem exists_eq_smul_one_of_commute_matrix_mul {J : Matrix ι ι K} (hJ : IsUnit J)
    (halt : ∀ x, x ⬝ᵥ (J *ᵥ x) = 0) (hcard : 2 < Fintype.card ι) {M : Matrix ι ι K}
    (hM : ∀ u v, u ⬝ᵥ (J *ᵥ v) = 1 →
      Commute M ((1 + vecMulVec u (J *ᵥ u)) * (1 + vecMulVec v (J *ᵥ v)))) :
    ∃ c : K, M = c • 1 := by
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_commute_transvection_mul
    (β := Matrix.toBilin' J) (f := Matrix.toLinAlgEquiv' M)
    (fun x => by rw [Matrix.toBilin'_apply']; exact halt x)
    (fun x hx => by
      obtain ⟨y, hy⟩ := (exists_dotProduct_mulVec_ne_zero hJ hx).1
      exact ⟨y, by rwa [Matrix.toBilin'_apply']⟩)
    (by rwa [Module.finrank_fintype_fun_eq_card])
    (fun u v huv => by
      rw [← toLinAlgEquiv'_transvection, ← toLinAlgEquiv'_transvection, ← map_mul]
      exact commute_toLinAlgEquiv' (hM u v (by rwa [Matrix.toBilin'_apply'] at huv)))
  exact ⟨c, eq_smul_one_of_toLinAlgEquiv' hc⟩


theorem dotProduct_separating {x : ι → K} (hx : ∀ y, x ⬝ᵥ y = 0) : x = 0 := by
  funext j
  have := hx (Pi.single j 1)
  rwa [dotProduct_single_one] at this


theorem exists_eq_smul_one_of_commute_dotProduct_mul {d : ι → K} (hdd : d ⬝ᵥ d = 1)
    (halt : ∀ x, d ⬝ᵥ x = 0 → x ⬝ᵥ x = 0) {M : Matrix ι ι K}
    (hg : ∀ u v, d ⬝ᵥ u = 0 → d ⬝ᵥ v = 0 → u ⬝ᵥ v = 1 →
      Commute M ((1 + vecMulVec u u) * (1 + vecMulVec v v)))
    {h : ι → K} (hh : d ⬝ᵥ h = 0) (hh0 : h ≠ 0)
    (hτ : Commute M (vecMulVec h d + vecMulVec d h)) : ∃ c : K, M = c • 1 := by
  obtain ⟨c, hc⟩ := eq_smul_one_of_commute_transvection_mul_of_commute_shear
    (β := Matrix.toBilin' (1 : Matrix ι ι K)) (f := Matrix.toLinAlgEquiv' M)
    (fun x y => by rw [toBilin'_one_apply_eq, toBilin'_one_apply_eq, dotProduct_comm])
    (fun x hx => dotProduct_separating fun y => by rw [← toBilin'_one_apply_eq]; exact hx y)
    (d := d) (by rw [toBilin'_one_apply_eq, hdd])
    (fun x hx => by
      rw [toBilin'_one_apply_eq] at hx ⊢
      exact halt x hx)
    (fun u v hu hv huv => by
      rw [← toLinAlgEquiv'_transvection_one, ← toLinAlgEquiv'_transvection_one, ← map_mul]
      rw [toBilin'_one_apply_eq] at hu hv huv
      exact commute_toLinAlgEquiv' (hg u v hu hv huv))
    (h := h) (by rw [toBilin'_one_apply_eq, hh]) hh0
    (by rw [← toLinAlgEquiv'_shear]; exact commute_toLinAlgEquiv' hτ)
  exact ⟨c, eq_smul_one_of_toLinAlgEquiv' hc⟩

end Matrix

end ClassicalLagrangian

end CFSG.SeitzReduction
