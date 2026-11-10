module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement MatrixGroups

theorem derivedSeries_two_semidirectProduct {N G : Type*} [CommGroup N] [Group G]
    (φ : G →* MulAut N) (hG : ∀ a b : G, a * b = b * a) : derivedSeries (N ⋊[φ] G) 2 = ⊥ := by
  have h1 : derivedSeries (N ⋊[φ] G) 1 ≤ SemidirectProduct.inl.range := by
    rw [derivedSeries_one, _root_.commutator_def, SemidirectProduct.range_inl_eq_ker_rightHom]
    exact Subgroup.commutator_le.2 fun x _ y _ => by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hG _ _
  rw [derivedSeries_succ, eq_bot_iff]
  refine (Subgroup.commutator_mono h1 h1).trans (Subgroup.commutator_le.2 ?_)
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul, mul_comm]

variable (K : Type*) [Field K]

@[expose] def unitsRingAut : RingAut K →* MulAut Kˣ where
  toFun σ := Units.mapEquiv σ.toMulEquiv
  map_one' := MulEquiv.ext fun _ => Units.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Units.ext rfl

@[expose] def scalarSemilinearHom : Kˣ ⋊[unitsRingAut K] RingAut K →* Equiv.Perm K where
  toFun x :=
    { toFun := fun c => x.left * x.right c
      invFun := fun c => x.right.symm (((x.left⁻¹ : Kˣ) : K) * c)
      left_inv := fun c => by simp
      right_inv := fun c => by simp }
  map_one' := Equiv.ext fun c => by
    change ((1 : Kˣ) : K) * c = c
    rw [Units.val_one, one_mul]
  map_mul' x y := Equiv.ext fun c => by
    change ((x.left * unitsRingAut K x.right y.left : Kˣ) : K) * x.right (y.right c) =
      x.left * x.right (y.left * y.right c)
    rw [Units.val_mul, map_mul, mul_assoc]
    rfl

theorem ringAut_mul_comm [Finite K] (σ τ : RingAut K) : σ * τ = τ * σ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hK⟩ := FiniteField.card' K
  have hcyc := (card_ringAut_and_isCyclic hp K (by rw [Nat.card_eq_fintype_card, hK])).2
  exact hcyc.commGroup.mul_comm σ τ

theorem derivedSeries_two_scalarSemilinearPerm [Finite K] :
    derivedSeries (scalarSemilinearPerm K) 2 = ⊥ := by
  let f := (scalarSemilinearHom K).codRestrict (scalarSemilinearPerm K)
    fun x => ⟨x.left, x.right, fun _ => rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨π, a, σ, h⟩
    exact ⟨⟨a, σ⟩, Subtype.ext (Equiv.ext fun c => (h c).symm)⟩
  rw [← map_derivedSeries_eq hf, derivedSeries_two_semidirectProduct _ (ringAut_mul_comm K),
    Subgroup.map_bot]

theorem exceptional_central_SL2_pair_stabilizer {K : Type*} [Field K] [Finite K]
    {L : Type*} [Group L] (ρ : SL(2, K) →* L) (hρ : Function.Surjective ρ)
    (hker : ∀ g : SL(2, K), ρ g = 1 → ∃ l : Kˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K)) :
    derivedSeries (pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ)) 2 = ⊥ := by
  obtain ⟨-, Φ, hΦ, -⟩ := central_SL2_root_pair_semilinear_parameters ρ hρ hker
  have h := map_derivedSeries_le_derivedSeries Φ 2
  rwa [derivedSeries_two_scalarSemilinearPerm, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ hΦ] at h

@[expose] def scalarAddAut : Subgroup (Multiplicative (AddAut K)) where
  carrier := {f | ∃ c : Kˣ, ∀ x, f.toAdd x = c * x}
  one_mem' := ⟨1, fun x => by simp⟩
  mul_mem' := by
    rintro f g ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, fun x => ?_⟩
    change f.toAdd (g.toAdd x) = _
    rw [hd, hc, Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro f ⟨c, hc⟩
    refine ⟨c⁻¹, fun x => ?_⟩
    change f.toAdd.symm x = _
    rw [AddEquiv.symm_apply_eq, hc, Units.mul_inv_cancel_left]

variable {K}

theorem conj_scalarAddAut {f : Multiplicative (AddAut K)} {a : Kˣ} {σ : K ≃+* K}
    (hf : ∀ x, f.toAdd x = a * σ x) (c : K) (y : K) :
    f.toAdd (c * f.toAdd.symm y) = σ c * y := by
  have hy : (a : K) * σ (f.toAdd.symm y) = y := by rw [← hf, AddEquiv.apply_symm_apply]
  rw [hf, map_mul]
  conv_rhs => rw [← hy]
  ring

theorem mem_normalizer_scalarAddAut_iff [Finite K] (f : Multiplicative (AddAut K)) :
    f ∈ Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) ↔
      ∃ (a : Kˣ) (σ : K ≃+* K), ∀ x, f.toAdd x = a * σ x := by
  constructor
  · intro hN
    have hψ : ∀ c : Kˣ, ∃ d : K, ∀ x, f.toAdd (c * x) = d * f.toAdd x := by
      intro c
      have hc : Multiplicative.ofAdd (AddAut.mulLeft c) ∈ scalarAddAut K := ⟨c, fun x => rfl⟩
      obtain ⟨d, hd⟩ := (Subgroup.mem_normalizer_iff.1 hN _).1 hc
      refine ⟨d, fun x => ?_⟩
      have := hd (f.toAdd x)
      change f.toAdd (c • f.toAdd.symm (f.toAdd x)) = _ at this
      rwa [AddEquiv.symm_apply_apply, Units.smul_def, smul_eq_mul] at this
    have hf0 : f.toAdd 0 = 0 := map_zero _
    have hf1 : f.toAdd 1 ≠ 0 := fun h => one_ne_zero (f.toAdd.injective (h.trans hf0.symm))
    have hmul : ∀ c x : K, (f.toAdd 1)⁻¹ * f.toAdd (c * x) =
        ((f.toAdd 1)⁻¹ * f.toAdd c) * ((f.toAdd 1)⁻¹ * f.toAdd x) := by
      intro c x
      by_cases hc : c = 0
      · rw [hc, zero_mul, hf0, mul_zero, zero_mul]
      · obtain ⟨d, hd⟩ := hψ (Units.mk0 c hc)
        have h1 := hd 1
        rw [Units.val_mk0, mul_one] at h1
        rw [Units.val_mk0] at hd
        rw [hd, h1]
        field_simp
    let σr : K →+* K :=
      { toFun := fun x => (f.toAdd 1)⁻¹ * f.toAdd x
        map_one' := inv_mul_cancel₀ hf1
        map_mul' := hmul
        map_zero' := by rw [hf0, mul_zero]
        map_add' := fun x y => by rw [map_add, mul_add] }
    refine ⟨Units.mk0 _ hf1, RingEquiv.ofBijective σr
      ⟨σr.injective, Finite.surjective_of_injective σr.injective⟩, fun x => ?_⟩
    change f.toAdd x = f.toAdd 1 * ((f.toAdd 1)⁻¹ * f.toAdd x)
    rw [mul_inv_cancel_left₀ hf1]
  · rintro ⟨a, σ, hf⟩
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨?_, ?_⟩
    · rintro ⟨c, hc⟩
      refine ⟨Units.map σ.toMonoidHom c, fun y => ?_⟩
      change f.toAdd (h.toAdd (f.toAdd.symm y)) = _
      rw [hc, conj_scalarAddAut hf]
      rfl
    · rintro ⟨d, hd⟩
      refine ⟨Units.map σ.symm.toMonoidHom d, fun y => ?_⟩
      have hy := hd (f.toAdd y)
      change f.toAdd (h.toAdd (f.toAdd.symm (f.toAdd y))) = _ at hy
      rw [AddEquiv.symm_apply_apply, hf, hf] at hy
      have hy' : σ (h.toAdd y) = d * σ y := mul_left_cancel₀ a.ne_zero (by rw [hy]; ring)
      have hσ := congrArg σ.symm hy'
      rw [RingEquiv.symm_apply_apply, map_mul, RingEquiv.symm_apply_apply] at hσ
      rw [hσ]
      rfl

theorem small_Ree_additive_scalar_normalizer (p n : ℕ) (hp : p.Prime) (_hn : 1 ≤ n)
    (K : Type*) [Field K] (hK : Nat.card K = p ^ n) :
    (∀ f : Multiplicative (AddAut K),
      f ∈ Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) ↔
        ∃ (a : Kˣ) (σ : K ≃+* K), ∀ x, f.toAdd x = a * σ x) ∧
    derivedSeries (Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K)))) 2 =
      ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero n hp.ne_zero)
  refine ⟨mem_normalizer_scalarAddAut_iff, ?_⟩
  set N := Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K)))
  have hmem : ∀ f : N, ((f : Multiplicative (AddAut K)).toAdd.toEquiv : Equiv.Perm K) ∈
      scalarSemilinearPerm K := fun f => (mem_normalizer_scalarAddAut_iff _).1 f.2
  let Ψ : N →* scalarSemilinearPerm K :=
    { toFun := fun f => ⟨(f : Multiplicative (AddAut K)).toAdd.toEquiv, hmem f⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hΨ : Function.Injective Ψ := fun f g h => Subtype.ext (by
    have h' := congrArg (fun π : scalarSemilinearPerm K => ((π : Equiv.Perm K) : K → K)) h
    exact congrArg Multiplicative.ofAdd (AddEquiv.ext fun x => congrFun h' x))
  have h := map_derivedSeries_le_derivedSeries Ψ 2
  rwa [derivedSeries_two_scalarSemilinearPerm, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ hΨ] at h


end CFSG.LocalAnalysis.ComponentInitial
