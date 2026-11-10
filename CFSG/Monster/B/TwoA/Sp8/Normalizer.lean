
module


public import CFSG.Monster.B.TwoA.Sp8.GenAction

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Co2Inv

theorem xhat_mem_A8_e0 :
    xhat ∈ A8 := by
  rw [← aEquiv_e0]
  exact (aEquiv _).2

theorem orderOf_rK :
    orderOf rK = 2 :=
  orderOf_eq_prime (by rw [sq]; exact rK_mul_self) rK_ne_one

theorem mem_H1_of_normalizer
    {n : Dfull} (hn : n ∈ NA8) (hx : n * xhat * n⁻¹ = xhat) :
    n ∈ H1 := by
  have hJ : n ∈ Jhat := by
    rw [← centralizer_xhat]
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc n * xhat = n * xhat * n⁻¹ * n := by group
      _ = xhat * n := by rw [hx]
  refine (mem_H1_iff n).2 ⟨hJ, ?_⟩
  have hc : n * ghat8 * n⁻¹ ∈ A8 := conj_mem_A8 hn ghat8_mem_A8
  have hcJ : n * ghat8 * n⁻¹ ∈ Jhat := A8_le_Jhat hc
  have himg : jhatToKv0 ⟨n * ghat8 * n⁻¹, hcJ⟩ ∈ Subgroup.zpowers rK := by
    rw [← map_A8]
    exact ⟨⟨_, hcJ⟩, hc, rfl⟩
  have he : (⟨n * ghat8 * n⁻¹, hcJ⟩ : Jhat) =
      ⟨n, hJ⟩ * ⟨ghat8, ghat8_mem_Jhat⟩ * (⟨n, hJ⟩ : Jhat)⁻¹ := rfl
  rw [he, map_mul, map_mul, map_inv, jhatToKv0_ghat8] at himg
  rcases (Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_rK).1 himg with h1 | h2
  · exfalso
    apply rK_ne_one
    have := congrArg (fun k => (jhatToKv0 ⟨n, hJ⟩)⁻¹ * k * jhatToKv0 ⟨n, hJ⟩) h1
    simpa [mul_assoc] using this
  · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc jhatToKv0 ⟨n, hJ⟩ * rK =
        jhatToKv0 ⟨n, hJ⟩ * rK * (jhatToKv0 ⟨n, hJ⟩)⁻¹ * jhatToKv0 ⟨n, hJ⟩ := by group
      _ = rK * jhatToKv0 ⟨n, hJ⟩ := by rw [h2]

theorem H1_le_centralizer_xhat :
    H1 ≤ Subgroup.centralizer {xhat} := by
  rw [centralizer_xhat]
  exact H1_le_Jhat

theorem normalizer_A8_eq :
    Subgroup.normalizer (A8 : Set Dfull) = Xgrp := by
  refine le_antisymm (fun n hn => ?_) Xgrp_le_normalizer
  have h1 : n * xhat * n⁻¹ ∈ A8 := conj_mem_A8 hn xhat_mem_A8_e0
  have h2 : n * xhat * n⁻¹ ≠ 1 := fun h => TwoA.xhat_ne_one (by
    have := congrArg (fun y => n⁻¹ * y * n) h
    simpa [mul_assoc] using this)
  obtain ⟨g, hg, hgx⟩ := Xgrp_transitive h1 xhat_mem_A8_e0 h2 TwoA.xhat_ne_one
  have hgn : g * n ∈ H1 := mem_H1_of_normalizer
    (Subgroup.mul_mem _ (Xgrp_le_normalizer hg) hn) (by
      calc g * n * xhat * (g * n)⁻¹ = g * (n * xhat * n⁻¹) * g⁻¹ := by group
        _ = xhat := hgx)
  have e : n = g⁻¹ * (g * n) := by group
  rw [e]
  exact Xgrp.mul_mem (Xgrp.inv_mem hg) (H1_le_Xgrp hgn)

theorem Xgrp_inf_centralizer_xhat :
    Xgrp ⊓ Subgroup.centralizer {xhat} = H1 := by
  refine le_antisymm (fun n hn => ?_) (le_inf H1_le_Xgrp H1_le_centralizer_xhat)
  refine mem_H1_of_normalizer (Xgrp_le_normalizer hn.1) ?_
  have := Subgroup.mem_centralizer_singleton_iff.1 hn.2
  calc n * xhat * n⁻¹ = xhat * n * n⁻¹ := by rw [← this]
    _ = xhat := by group

@[expose] def rhoX :
    Xgrp →* (V8 ≃ₗ[ZMod 2] V8) :=
  conjHom.comp (Subgroup.inclusion Xgrp_le_normalizer)

theorem range_rhoX :
    rhoX.range = (Xgrp.subgroupOf NA8).map conjHom := by
  ext f
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion Xgrp_le_normalizer x, x.2, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩

theorem rhoX_mem_Sp
    (x : Xgrp) : rhoX x ∈ TauCeti.BilinForm.isometryGroup b0 :=
  conjImage_X_le (range_rhoX ▸ ⟨x, rfl⟩)

@[expose] def rhoXSp :
    Xgrp →* TauCeti.BilinForm.isometryGroup b0 :=
  rhoX.codRestrict _ rhoX_mem_Sp

theorem coe_rhoXSp
    (x : Xgrp) :
    ((rhoXSp x : TauCeti.BilinForm.isometryGroup b0) : V8 ≃ₗ[ZMod 2] V8) = rhoX x := rfl

theorem aEquiv_rhoX
    (x : Xgrp) (v : V8) :
    (aEquiv (Multiplicative.ofAdd (rhoX x v)) : Dfull) =
      x * aEquiv (Multiplicative.ofAdd v) * (x : Dfull)⁻¹ :=
  aEquiv_conjHom _ v

theorem rhoX_e0_iff
    (x : Xgrp) : rhoX x e0 = e0 ↔ (x : Dfull) ∈ H1 := by
  rw [← Xgrp_inf_centralizer_xhat]
  constructor
  · intro h
    refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have e := aEquiv_rhoX x e0
    rw [h, aEquiv_e0] at e
    calc (x : Dfull) * xhat = x * xhat * (x : Dfull)⁻¹ * x := by group
      _ = xhat * x := by rw [← e]
  · intro h
    apply aEquiv_coe_injective
    rw [aEquiv_rhoX, aEquiv_e0]
    have := Subgroup.mem_centralizer_singleton_iff.1 h.2
    calc (x : Dfull) * xhat * (x : Dfull)⁻¹ = xhat * x * (x : Dfull)⁻¹ := by rw [← this]
      _ = xhat := by group

@[expose, instance_reducible] def xAction :
    MulAction Xgrp V8 := MulAction.compHom V8 rhoX

attribute [local instance] xAction

theorem card_mul255 {a b c : ℕ} (h : b * a = c) (hb : b = 2 ^ 23 * 743178240) (ha : a = 255) :
    c = 1589728887019929600 := by
  subst ha
  subst hb
  omega

theorem card_div2 {a b c : ℕ} (h : a * b = c) (hb : b = 47377612800)
    (hc : c = 1589728887019929600) : a = 2 ^ 25 := by
  subst hb
  subst hc
  omega


attribute [local instance] xAction

theorem xAction_smul
    (x : Xgrp) (v : V8) : x • v = rhoX x v := rfl

theorem orbit_Xgrp_e0 :
    MulAction.orbit Xgrp e0 = {v : V8 | v ≠ 0} := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    show rhoX x e0 ≠ 0
    rw [LinearEquiv.map_ne_zero_iff]
    exact Pi.single_ne_zero_iff.2 one_ne_zero
  · intro hv
    obtain ⟨f, hf, hfv⟩ := exists_conjImage_X hv
    rw [← conjImage_X, ← range_rhoX] at hf
    obtain ⟨x, rfl⟩ := hf
    exact ⟨x, hfv⟩

theorem stabilizer_Xgrp_e0 :
    MulAction.stabilizer Xgrp e0 = H1.subgroupOf Xgrp := by
  ext x
  rw [MulAction.mem_stabilizer_iff, xAction_smul, Subgroup.mem_subgroupOf, rhoX_e0_iff]

theorem natCard_H1 :
    Nat.card H1 = 2 ^ 23 * 743178240 := by
  rw [H1, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    natCard_comap_of_surjective jhatToKv0_surjective, ker_jhatToKv0,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ehat_le_Jhat).toEquiv, natCard_Ehat, natCard_Cr]

theorem natCard_Xgrp :
    Nat.card Xgrp = 1589728887019929600 := by
  have hi := MulAction.index_stabilizer Xgrp e0
  have hc := (MulAction.stabilizer Xgrp e0).card_mul_index
  have hi' : (MulAction.stabilizer Xgrp e0).index = 255 :=
    hi.trans ((congrArg Set.ncard orbit_Xgrp_e0).trans ncard_nonzero)
  have hs : Nat.card (MulAction.stabilizer Xgrp e0) = 2 ^ 23 * 743178240 :=
    (congrArg (fun H : Subgroup Xgrp => Nat.card H) stabilizer_Xgrp_e0).trans
      ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe H1_le_Xgrp).toEquiv).trans natCard_H1)
  exact card_mul255 hc hs hi'


theorem rhoXSp_surjective :
    Function.Surjective rhoXSp := by
  intro s
  have hs0 : (s : V8 ≃ₗ[ZMod 2] V8) e0 ≠ 0 := by
    rw [LinearEquiv.map_ne_zero_iff]
    exact Pi.single_ne_zero_iff.2 one_ne_zero
  have horb : (s : V8 ≃ₗ[ZMod 2] V8) e0 ∈ MulAction.orbit Xgrp e0 := by
    rw [orbit_Xgrp_e0]
    exact hs0
  obtain ⟨x, hx⟩ := horb
  have hx' : rhoX x e0 = (s : V8 ≃ₗ[ZMod 2] V8) e0 := hx
  have hst : (rhoX x)⁻¹ * s ∈ SpX := by
    refine mem_SpX.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (rhoX_mem_Sp x)) s.2, ?_⟩
    rw [LinearEquiv.mul_apply, ← hx']
    exact (rhoX x).symm_apply_apply e0
  rw [← conjImage_H1_eq] at hst
  obtain ⟨n, hn, hnf⟩ := hst
  have hnX : (n : Dfull) ∈ Xgrp := H1_le_Xgrp (Subgroup.mem_subgroupOf.1 hn)
  refine ⟨x * ⟨n, hnX⟩, Subtype.ext ?_⟩
  rw [map_mul, Subgroup.coe_mul, coe_rhoXSp, coe_rhoXSp]
  have e : rhoX ⟨n, hnX⟩ = conjHom n := rfl
  rw [e, hnf, mul_inv_cancel_left]

theorem rhoX_eq_one_iff
    (x : Xgrp) : rhoX x = 1 ↔ (x : Dfull) ∈ Lgrp := by
  rw [Lgrp, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    obtain ⟨v, hv⟩ := aEquiv.surjective ⟨a, ha⟩
    have ha' : a = aEquiv v := congrArg Subtype.val hv.symm
    have e := aEquiv_rhoX x (Multiplicative.toAdd v)
    rw [h, ofAdd_toAdd] at e
    have e2 : (aEquiv v : Dfull) = x * aEquiv v * (x : Dfull)⁻¹ := e
    rw [ha']
    calc (aEquiv v : Dfull) * x = x * aEquiv v * (x : Dfull)⁻¹ * x := by rw [← e2]
      _ = x * aEquiv v := by group
  · intro h
    refine LinearEquiv.ext fun v => aEquiv_coe_injective ?_
    rw [aEquiv_rhoX, ← h _ (aEquiv _).2]
    show (aEquiv (Multiplicative.ofAdd v) : Dfull) * x * (x : Dfull)⁻¹ =
      aEquiv (Multiplicative.ofAdd v)
    group

theorem Lgrp_le_Xgrp :
    Lgrp ≤ Xgrp := by
  rw [← normalizer_A8_eq]
  exact Subgroup.centralizer_le_normalizer _

theorem ker_rhoXSp :
    rhoXSp.ker = Lgrp.subgroupOf Xgrp := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← rhoX_eq_one_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem natCard_Lgrp :
    Nat.card Lgrp = 2 ^ 25 := by
  have h := natCard_ker_mul_range rhoXSp
  have hr : Nat.card rhoXSp.range = 47377612800 :=
    ((Subgroup.card_eq_iff_eq_top _).2 (MonoidHom.range_eq_top.2 rhoXSp_surjective)).trans
      natCard_Sp
  have hk : Nat.card rhoXSp.ker = Nat.card Lgrp :=
    (congrArg (fun H : Subgroup Xgrp => Nat.card H) ker_rhoXSp).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Lgrp_le_Xgrp).toEquiv)
  exact hk.symm.trans (card_div2 h hr natCard_Xgrp)


theorem A8_le_Lgrp :
    A8 ≤ Lgrp := fun a ha => by
  rw [Lgrp, Subgroup.mem_centralizer_iff]
  intro b hb
  have := A8_comm ⟨b, hb⟩ ⟨a, ha⟩
  exact congrArg Subtype.val this


end CFSG.Monster.B.TwoA.Sp8
