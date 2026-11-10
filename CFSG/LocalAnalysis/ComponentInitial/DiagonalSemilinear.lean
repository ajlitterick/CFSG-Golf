module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.CharP.CharAndCard

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement

theorem card_ringAut_and_isCyclic {p n : ℕ} (hp : p.Prime) (K : Type*) [Field K] [Finite K]
    (hK : Nat.card K = p ^ n) : Nat.card (RingAut K) = n ∧ IsCyclic (RingAut K) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let e : RingAut K ≃* (K ≃ₐ[ZMod p] K) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) fun x =>
        DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod p) K))
          (algebraMap (ZMod p) K)) x
      invFun := fun σ => σ.toRingEquiv
      left_inv := fun _ => RingEquiv.ext fun _ => rfl
      right_inv := fun _ => AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  refine ⟨?_, isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective⟩
  rw [Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]
  apply Nat.pow_right_injective hp.two_le
  change p ^ Module.finrank (ZMod p) K = p ^ n
  rw [FiniteField.pow_finrank_eq_natCard, hK]

variable (K : Type*) [Field K] (d : ℕ)

@[expose] def unitsPiRingAut : RingAut K →* MulAut (Fin d → Kˣ) where
  toFun σ := MulEquiv.piCongrRight fun _ => Units.mapEquiv σ.toMulEquiv
  map_one' := MulEquiv.ext fun _ => funext fun _ => Units.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => funext fun _ => Units.ext rfl

@[expose] def semilinearAddEquiv (a : Fin d → Kˣ) (σ : RingAut K) :
    (Fin d → K) ≃+ (Fin d → K) where
  toFun x j := a j * σ (x j)
  invFun x j := σ.symm (((a j)⁻¹ : Kˣ) * x j)
  left_inv x := funext fun j => by simp
  right_inv x := funext fun j => by simp
  map_add' x y := funext fun j => by simp [mul_add]

variable (p : ℕ) [Module (ZMod p) K]

@[expose] def semilinearGL (a : Fin d → Kˣ) (σ : RingAut K) :
    LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    { (semilinearAddEquiv K d a σ).toAddMonoidHom.toZModLinearMap p with
      invFun := (semilinearAddEquiv K d a σ).symm
      left_inv := (semilinearAddEquiv K d a σ).left_inv
      right_inv := (semilinearAddEquiv K d a σ).right_inv }


theorem semilinearGL_mul (a b : Fin d → Kˣ) (σ τ : RingAut K) :
    semilinearGL K d p a σ * semilinearGL K d p b τ =
      semilinearGL K d p (a * unitsPiRingAut K d σ b) (σ * τ) := by
  refine Units.ext (LinearMap.ext fun x => funext fun j => ?_)
  change (a j : K) * σ ((b j : K) * τ (x j)) = ((a j : K) * σ (b j)) * σ (τ (x j))
  rw [map_mul, mul_assoc]

@[expose] def semilinearHom : (Fin d → Kˣ) ⋊[unitsPiRingAut K d] RingAut K →*
    LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K) where
  toFun g := semilinearGL K d p g.left g.right
  map_one' := Units.ext (LinearMap.ext fun x => funext fun j => by
    change ((1 : Kˣ) : K) * x j = x j
    rw [Units.val_one, one_mul])
  map_mul' g h := by
    rw [semilinearGL_mul]
    rfl


@[expose] def diagSemilinearGroup : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K)) :=
  (semilinearHom K d p).range

@[expose] def diagUnitGroup : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K)) :=
  ((semilinearHom K d p).comp SemidirectProduct.inl).range


instance diagUnitGroup_subgroupOf_normal :
    ((diagUnitGroup K d p).subgroupOf (diagSemilinearGroup K d p)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨a, ha⟩ := hx
  obtain ⟨y, hy⟩ := g.2
  have hn : y * SemidirectProduct.inl a * y⁻¹ ∈
      (SemidirectProduct.inl :
        (Fin d → Kˣ) →* (Fin d → Kˣ) ⋊[unitsPiRingAut K d] RingAut K).range := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      SemidirectProduct.rightHom_inl, mul_one, mul_inv_cancel]
  obtain ⟨b, hb⟩ := hn
  refine ⟨b, ?_⟩
  change semilinearHom K d p (SemidirectProduct.inl b) =
    (g : LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K)) * x * (g : _)⁻¹
  rw [hb, map_mul, map_mul, map_inv, hy,
    show semilinearHom K d p (SemidirectProduct.inl a) = x from ha]
  rfl


end CFSG.LocalAnalysis.ComponentInitial
