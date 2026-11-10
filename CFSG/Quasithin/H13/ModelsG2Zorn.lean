module

public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped Matrix

section General

variable {K : Type*} [CommRing K]

@[expose] def zornIdentity : quasithinZorn K := (1, 0, 0, 1)

theorem zornMul_identity_left (y : quasithinZorn K) : quasithinZornMul zornIdentity y = y := by
  obtain ⟨r, u, v, s⟩ := y
  simp only [quasithinZornMul, zornIdentity, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, one_mul, mul_zero, zero_add]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> funext i <;>
    fin_cases i <;> simp [quasithinCross]

theorem zornMul_identity_right (y : quasithinZorn K) : quasithinZornMul y zornIdentity = y := by
  obtain ⟨r, u, v, s⟩ := y
  simp only [quasithinZornMul, zornIdentity, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, mul_one, one_mul, zero_add]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> funext i <;>
    fin_cases i <;> simp [quasithinCross]


variable (K) in
@[expose] def zornAut : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K) where
  carrier := {g | ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y)}
  mul_mem' {g h} hg hh x y := by
    change g (h (quasithinZornMul x y)) = quasithinZornMul (g (h x)) (g (h y))
    rw [hh, hg]
  one_mem' _ _ := rfl
  inv_mem' {g} hg x y := by
    have h1 := hg (g.symm x) (g.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    change g.symm (quasithinZornMul x y) = quasithinZornMul (g.symm x) (g.symm y)
    rw [← h1, LinearEquiv.symm_apply_apply]


theorem zornAut_map_identity {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : g ∈ zornAut K) :
    g zornIdentity = zornIdentity := by
  have h := hg zornIdentity (g.symm zornIdentity)
  rw [zornMul_identity_left, LinearEquiv.apply_symm_apply, zornMul_identity_right] at h
  exact h.symm

variable (K) in
@[expose] def zornCoord : quasithinZorn K ≃ₗ[K] (Fin 8 → K) where
  toFun x := ![x.1, x.2.1 0, x.2.1 1, x.2.1 2, x.2.2.1 0, x.2.2.1 1, x.2.2.1 2, x.2.2.2]
  invFun w := (w 0, ![w 1, w 2, w 3], ![w 4, w 5, w 6], w 7)
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' c x := by
    funext i
    fin_cases i <;> rfl
  left_inv x := by
    obtain ⟨a, u, v, b⟩ := x
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> funext i <;> fin_cases i <;> rfl
  right_inv w := by
    funext i
    fin_cases i <;> rfl


@[expose] def zornBasisVec (i : Fin 8) : quasithinZorn K :=
  (zornCoord K).symm (Pi.single i 1)

variable (K) in
@[expose] noncomputable def zornBasis : Module.Basis (Fin 8) K (quasithinZorn K) :=
  (Pi.basisFun K (Fin 8)).map (zornCoord K).symm

theorem zornBasis_apply (i : Fin 8) : zornBasis K i = zornBasisVec i := by
  simp [zornBasis, zornBasisVec]


end General


@[expose] def zornX0 : quasithinZorn (ZMod 3) := (0, ![0, 0, 1], ![0, 0, 2], 0)

@[expose] def zornY0 : quasithinZorn (ZMod 3) := (0, ![0, 1, 0], ![0, 2, 0], 0)

@[expose] def zornZ0 : quasithinZorn (ZMod 3) := (0, ![1, 0, 1], ![1, 0, 1], 0)

@[expose] def zornSet1 : Set (quasithinZorn (ZMod 3)) :=
  {x | quasithinZornMul x x = -zornIdentity}

@[expose] def zornSet2 : Set (quasithinZorn (ZMod 3)) :=
  {y | quasithinZornMul y y = -zornIdentity ∧
    quasithinZornMul zornX0 y + quasithinZornMul y zornX0 = 0}

@[expose] def zornSet3 : Set (quasithinZorn (ZMod 3)) :=
  {z | quasithinZornMul z z = -zornIdentity ∧
    quasithinZornMul zornX0 z + quasithinZornMul z zornX0 = 0 ∧
    quasithinZornMul zornY0 z + quasithinZornMul z zornY0 = 0 ∧
    quasithinZornMul (quasithinZornMul zornX0 zornY0) z +
      quasithinZornMul z (quasithinZornMul zornX0 zornY0) = 0}

instance : DecidablePred (· ∈ zornSet1) := fun x => by
  unfold zornSet1
  infer_instance

instance : DecidablePred (· ∈ zornSet2) := fun x => by
  unfold zornSet2
  infer_instance

instance : DecidablePred (· ∈ zornSet3) := fun x => by
  unfold zornSet3
  infer_instance


@[expose] def zornWords : Fin 8 → quasithinZorn (ZMod 3) :=
  ![zornIdentity, zornX0, zornY0, quasithinZornMul zornX0 zornY0, zornZ0,
    quasithinZornMul zornX0 zornZ0, quasithinZornMul zornY0 zornZ0,
    quasithinZornMul (quasithinZornMul zornX0 zornY0) zornZ0]

@[expose] def zornWordsInv : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  !![2, 0, 0, 0, 0, 0, 0, 2;
    0, 0, 0, 2, 0, 0, 1, 0;
    0, 0, 2, 0, 0, 1, 0, 0;
    0, 2, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 1, 1, 0, 1, 0;
    1, 0, 1, 0, 0, 1, 0, 2;
    0, 1, 0, 2, 1, 0, 2, 0;
    1, 0, 2, 0, 0, 2, 0, 2]

theorem zornBasisVec_eq_sum :
    ∀ k : Fin 8, zornBasisVec k = ∑ j, zornWordsInv j k • zornWords j := by
  decide +kernel

theorem eq_one_of_fix {g : quasithinZorn (ZMod 3) ≃ₗ[ZMod 3] quasithinZorn (ZMod 3)}
    (hg : g ∈ zornAut (ZMod 3)) (hx : g zornX0 = zornX0) (hy : g zornY0 = zornY0)
    (hz : g zornZ0 = zornZ0) : g = 1 := by
  have hw : ∀ j, g (zornWords j) = zornWords j := by
    intro j
    fin_cases j <;> simp [zornWords, hg _ _, zornAut_map_identity hg, hx, hy, hz]
  have hb : ∀ k, g (zornBasisVec k) = zornBasisVec k := by
    intro k
    rw [zornBasisVec_eq_sum k, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hw j]
  have hlin : (g : quasithinZorn (ZMod 3) →ₗ[ZMod 3] quasithinZorn (ZMod 3)) = LinearMap.id :=
    (zornBasis (ZMod 3)).ext fun k => by
      rw [zornBasis_apply, LinearEquiv.coe_coe, hb k, LinearMap.id_apply]
  exact LinearEquiv.ext fun v => by
    have := LinearMap.congr_fun hlin v
    simpa using this

instance : Finite (quasithinZorn (ZMod 3) ≃ₗ[ZMod 3] quasithinZorn (ZMod 3)) :=
  Finite.of_injective (fun g => (g : quasithinZorn (ZMod 3) → quasithinZorn (ZMod 3)))
    DFunLike.coe_injective


end CFSG.Quasithin.H13
