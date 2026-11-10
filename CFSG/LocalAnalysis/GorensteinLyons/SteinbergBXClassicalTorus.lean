module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Equiv Subgroup

section TorusVec

variable {M : Type*} [CommGroup M] {n : ℕ}

@[expose] def torusVec (ζ : M) (i d : Fin n) : Fin n → M :=
  Pi.mulSingle i ζ * Pi.mulSingle d ζ⁻¹

theorem torusVec_apply (ζ : M) (i d j : Fin n) :
    torusVec ζ i d j = (if j = i then ζ else 1) * (if j = d then ζ⁻¹ else 1) := by
  simp only [torusVec, Pi.mul_apply, Pi.mulSingle_apply]

theorem prod_torusVec (ζ : M) (i d : Fin n) : ∏ j, torusVec ζ i d j = 1 := by
  simp only [torusVec_apply, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
    ite_true, mul_inv_cancel]

theorem torusVec_apply_of_ne {ζ : M} {i d j : Fin n} (hi : j ≠ i) (hd : j ≠ d) :
    torusVec ζ i d j = 1 := by
  rw [torusVec_apply, ite_eq_right hi, ite_eq_right hd, mul_one]

theorem torusVec_apply_left {ζ : M} {i d : Fin n} (hid : i ≠ d) : torusVec ζ i d i = ζ := by
  rw [torusVec_apply, ite_eq_left rfl, ite_eq_right hid, mul_one]

theorem torusVec_apply_right {ζ : M} {i d : Fin n} (hid : i ≠ d) :
    torusVec ζ i d d = ζ⁻¹ := by
  rw [torusVec_apply, ite_eq_right (Ne.symm hid), ite_eq_left rfl, one_mul]

theorem torusVec_zpow (ζ : M) (i d : Fin n) (a : ℤ) :
    torusVec ζ i d ^ a = torusVec (ζ ^ a) i d := by
  ext j
  rw [Pi.pow_apply, torusVec_apply, torusVec_apply, mul_zpow]
  split_ifs <;> simp

theorem torusVec_one (i d : Fin n) : torusVec (1 : M) i d = 1 := by
  simp [torusVec]

theorem torusVec_comp_swap_self (ζ : M) {i d : Fin n} (hid : i ≠ d) :
    torusVec ζ i d ∘ swap i d = (torusVec ζ i d)⁻¹ := by
  ext k
  rw [Function.comp_apply, Pi.inv_apply]
  by_cases hki : k = i
  · subst hki
    rw [swap_apply_left, torusVec_apply_right hid, torusVec_apply_left hid]
  · by_cases hkd : k = d
    · subst hkd
      rw [swap_apply_right, torusVec_apply_left hid, torusVec_apply_right hid, inv_inv]
    · rw [swap_apply_of_ne_of_ne hki hkd, torusVec_apply_of_ne hki hkd, inv_one]

theorem torusVec_comp_swap (ζ : M) {i j d : Fin n} (hid : i ≠ d) (hjd : j ≠ d) :
    torusVec ζ i d ∘ swap i j = torusVec ζ j d := by
  ext k
  rw [Function.comp_apply]
  by_cases hij : i = j
  · subst hij
    rw [swap_self, Equiv.refl_apply]
  by_cases hki : k = i
  · subst hki
    rw [swap_apply_left, torusVec_apply_of_ne (Ne.symm hij) hjd, torusVec_apply_of_ne hij hid]
  · by_cases hkj : k = j
    · subst hkj
      rw [swap_apply_right, torusVec_apply_left hid, torusVec_apply_left hjd]
    · rw [swap_apply_of_ne_of_ne hki hkj]
      by_cases hkd : k = d
      · subst hkd
        rw [torusVec_apply_right hid, torusVec_apply_right hjd]
      · rw [torusVec_apply_of_ne hki hkd, torusVec_apply_of_ne hkj hkd]

theorem torusVec_comp_swap_of_ne (ζ : M) {i d a b : Fin n} (hai : a ≠ i) (had : a ≠ d)
    (hbi : b ≠ i) (hbd : b ≠ d) : torusVec ζ i d ∘ swap a b = torusVec ζ i d := by
  ext k
  rw [Function.comp_apply]
  by_cases hka : k = a
  · subst hka
    rw [swap_apply_left, torusVec_apply_of_ne hbi hbd, torusVec_apply_of_ne hai had]
  · by_cases hkb : k = b
    · subst hkb
      rw [swap_apply_right, torusVec_apply_of_ne hai had, torusVec_apply_of_ne hbi hbd]
    · rw [swap_apply_of_ne_of_ne hka hkb]

end TorusVec

section Abstract

variable {S : Type*} [Group S] {M : Type*} [CommGroup M] {n : ℕ}

theorem torus_weyl_hypotheses (A : Subgroup (Fin n → M))
    (hAperm : ∀ (σ : Perm (Fin n)) (v : Fin n → M), v ∈ A → v ∘ σ ∈ A) (δ : A →* S)
    (hker : ∀ v : A, δ v = 1 → ∀ j k, (v : Fin n → M) j = (v : Fin n → M) k)
    (W : Fin n → Fin n → S)
    (hW : ∀ (a b : Fin n) (v : A), W a b * δ v * (W a b)⁻¹ =
      δ ⟨v ∘ swap a b, hAperm (swap a b) v v.2⟩)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {ζ : M} (hζ : orderOf ζ = p) {m : ℕ}
    (pos : Fin m → Fin n) (hpos : Function.Injective pos) (d e : Fin n) (hpd : ∀ i, pos i ≠ d)
    (hpe : ∀ i, pos i ≠ e) (hde : d ≠ e) (hτ : ∀ i, torusVec ζ (pos i) d ∈ A) :
    (∀ i, δ ⟨_, hτ i⟩ ^ p = 1) ∧ (∀ i, δ ⟨_, hτ i⟩ ≠ 1) ∧
      (∀ i j, Commute (δ ⟨_, hτ i⟩) (δ ⟨_, hτ j⟩)) ∧
      iSupIndep (fun i => zpowers (δ ⟨_, hτ i⟩)) ∧
      (∀ i, ∃ g : S, ∃ a : ℤ, ¬ (p : ℤ) ∣ 1 - a ∧ g * δ ⟨_, hτ i⟩ * g⁻¹ = δ ⟨_, hτ i⟩ ^ a) ∧
      (∀ i j, i ≠ j → ∃ g : S,
        (∃ a b : ℤ, ¬ (p : ℤ) ∣ a * b - 1 ∧ g * δ ⟨_, hτ i⟩ * g⁻¹ = δ ⟨_, hτ i⟩ ^ a ∧
          g * δ ⟨_, hτ j⟩ * g⁻¹ = δ ⟨_, hτ j⟩ ^ b) ∨
        (g * δ ⟨_, hτ i⟩ * g⁻¹ = δ ⟨_, hτ j⟩ ∧ g * δ ⟨_, hτ j⟩ * g⁻¹ = δ ⟨_, hτ i⟩)) := by
  set τ : Fin m → A := fun i => ⟨_, hτ i⟩ with hτdef
  have hτval : ∀ i, ((τ i : A) : Fin n → M) = torusVec ζ (pos i) d := fun i => rfl
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := fun h => by rw [h, orderOf_one] at hζ; exact hp.out.ne_one hζ.symm
  have hτord : ∀ i (a : ℤ), ζ ^ a = 1 → τ i ^ a = 1 := by
    intro i a ha
    apply Subtype.ext
    rw [SubgroupClass.coe_zpow, hτval, torusVec_zpow, ha, torusVec_one, OneMemClass.coe_one]
  have hcp : ∀ i, δ (τ i) ^ p = 1 := by
    intro i
    rw [← zpow_natCast, ← map_zpow, hτord i _ (by rw [zpow_natCast, hζp]), map_one]
  have hind : iSupIndep fun i => zpowers (δ (τ i)) := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_def]
    intro x hx hx'
    let T : Subgroup A :=
      { carrier := {v | (v : Fin n → M) (pos i) = (v : Fin n → M) e}
        mul_mem' := by
          intro v w hv hw
          change ((v * w : A) : Fin n → M) (pos i) = ((v * w : A) : Fin n → M) e
          rw [Subgroup.coe_mul, Pi.mul_apply, Pi.mul_apply, hv, hw]
        one_mem' := rfl
        inv_mem' := by
          intro v hv
          change ((v⁻¹ : A) : Fin n → M) (pos i) = ((v⁻¹ : A) : Fin n → M) e
          rw [Subgroup.coe_inv, Pi.inv_apply, Pi.inv_apply, hv] }
    have hle : (⨆ (j) (_ : j ≠ i), zpowers (δ (τ j))) ≤ T.map δ := by
      refine iSup₂_le fun j hj => ?_
      rw [zpowers_le]
      refine ⟨τ j, ?_, rfl⟩
      change ((τ j : A) : Fin n → M) (pos i) = ((τ j : A) : Fin n → M) e
      rw [hτval, torusVec_apply_of_ne (fun h => hj (hpos h).symm) (hpd i),
        torusVec_apply_of_ne (fun h => hpe j h.symm) (Ne.symm hde)]
    obtain ⟨w, hwT, hw⟩ := hle hx'
    obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp hx
    have h1 : δ (τ i ^ a * w⁻¹) = 1 := by rw [map_mul, map_inv, map_zpow, hw, mul_inv_cancel]
    have h2 := hker _ h1 (pos i) e
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow, Pi.mul_apply,
      Pi.inv_apply, Pi.pow_apply, hτval] at h2
    rw [torusVec_apply_left (hpd i), torusVec_apply_of_ne (Ne.symm (hpe i)) (Ne.symm hde),
      one_zpow, one_mul] at h2
    have hwT' : (w : Fin n → M) (pos i) = (w : Fin n → M) e := hwT
    rw [hwT', mul_inv_eq_iff_eq_mul, inv_mul_cancel] at h2
    rw [← map_zpow, hτord i a h2, map_one]
  have hc1 : ∀ i, δ (τ i) ≠ 1 := by
    intro i h
    have h2 := hker _ h (pos i) e
    rw [hτval, torusVec_apply_left (hpd i),
      torusVec_apply_of_ne (Ne.symm (hpe i)) (Ne.symm hde)] at h2
    exact hζ1 h2
  refine ⟨hcp, hc1, fun i j => (Commute.all (τ i) (τ j)).map δ, hind, fun i => ?_,
    fun i j hij => ?_⟩
  · refine ⟨W (pos i) d, -1, ?_, ?_⟩
    · intro h
      have h2 : (p : ℤ) ∣ 2 := by
        have : (1 : ℤ) - -1 = 2 := by norm_num
        rwa [this] at h
      have h2' : p ∣ 2 := by exact_mod_cast h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2')
    · rw [hW, zpow_neg_one, ← map_inv]
      congr 1
      exact Subtype.ext (show torusVec ζ (pos i) d ∘ swap (pos i) d = (torusVec ζ (pos i) d)⁻¹ from
        torusVec_comp_swap_self ζ (hpd i))
  · refine ⟨W (pos i) (pos j), Or.inr ⟨?_, ?_⟩⟩
    · rw [hW]
      congr 1
      exact Subtype.ext (torusVec_comp_swap ζ (hpd i) (hpd j))
    · rw [hW]
      congr 1
      apply Subtype.ext
      change torusVec ζ (pos j) d ∘ swap (pos i) (pos j) = torusVec ζ (pos i) d
      rw [swap_comm]
      exact torusVec_comp_swap ζ (hpd j) (hpd i)

end Abstract


section SignedPerm

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

theorem diagonal_mul_diagonal_comm (u v : Fin n → K) :
    diagonal u * diagonal v = diagonal v * diagonal u := by
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

theorem permMatrix_mul_diagonal' (w : Perm (Fin n)) (v : Fin n → K) :
    permMatrix n K w * diagonal v = diagonal (fun a => v (w⁻¹ a)) * permMatrix n K w := by
  ext a b
  rw [mul_diagonal, diagonal_mul, permMatrix_apply]
  split_ifs with h
  · rw [h, Perm.inv_eq_iff_eq.mpr rfl, one_mul, mul_one]
  · rw [zero_mul, mul_zero]

theorem signedPermMatrix_eq (w : Perm (Fin n)) :
    signedPermMatrix n K w =
      diagonal (fun a : Fin n => if (a : ℕ) = 0 then ((Perm.sign w : ℤ) : K) else 1) *
        permMatrix n K w :=
  rfl

theorem signedPermMatrix_mul_diagonal (w : Perm (Fin n)) (v : Fin n → K) :
    signedPermMatrix n K w * diagonal v =
      diagonal (fun a => v (w⁻¹ a)) * signedPermMatrix n K w := by
  rw [signedPermMatrix_eq, Matrix.mul_assoc, permMatrix_mul_diagonal', ← Matrix.mul_assoc,
    diagonal_mul_diagonal_comm, Matrix.mul_assoc]

theorem permMatrix_mul_permMatrix (w w' : Perm (Fin n)) :
    permMatrix n K w * permMatrix n K w' = permMatrix n K (w * w') := by
  rw [permMatrix_eq, permMatrix_eq, permMatrix_eq, ← Matrix.permMatrix_mul, _root_.mul_inv_rev]

theorem signedPermMatrix_apply (w : Perm (Fin n)) (a b : Fin n) :
    signedPermMatrix n K w a b =
      (if (a : ℕ) = 0 then ((Perm.sign w : ℤ) : K) else 1) * (if a = w b then 1 else 0) := by
  rw [signedPermMatrix_eq, diagonal_mul, permMatrix_apply]

theorem sign_diagonal_mul_self (w : Perm (Fin n)) :
    diagonal (fun a : Fin n => if (a : ℕ) = 0 then ((Perm.sign w : ℤ) : K) else 1) *
      diagonal (fun a : Fin n => if (a : ℕ) = 0 then ((Perm.sign w : ℤ) : K) else 1) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs
  · rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  · rw [mul_one]


theorem transpose_permMatrix_mul_self (w : Perm (Fin n)) :
    (permMatrix n K w)ᵀ * permMatrix n K w = 1 := by
  ext a b
  rw [mul_apply, one_apply]
  simp only [transpose_apply, permMatrix_apply]
  rw [Finset.sum_eq_single (w a)]
  · rw [ite_eq_left rfl, one_mul]
    by_cases hab : a = b
    · rw [ite_eq_left (by rw [hab]), ite_eq_left hab]
    · rw [ite_eq_right fun h => hab (w.injective h), ite_eq_right hab]
  · intro c _ hc
    rw [ite_eq_right hc, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem transpose_signedPermMatrix_mul_self (w : Perm (Fin n)) :
    (signedPermMatrix n K w)ᵀ * signedPermMatrix n K w = 1 := by
  rw [signedPermMatrix_eq, transpose_mul, diagonal_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (diagonal _), sign_diagonal_mul_self, Matrix.one_mul,
    transpose_permMatrix_mul_self]

end SignedPerm

section Linear

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable (F : Type*) [Field F] (n : ℕ)

@[expose] def prodOneUnits : Subgroup (Fin n → Fˣ) :=
  (MonoidHom.mk' (fun v : Fin n → Fˣ => ∏ j, v j) fun v w => by
    simp only [Pi.mul_apply, Finset.prod_mul_distrib]).ker

variable {F n}

theorem mem_prodOneUnits {v : Fin n → Fˣ} : v ∈ prodOneUnits F n ↔ ∏ j, v j = 1 :=
  MonoidHom.mem_ker

theorem comp_mem_prodOneUnits (σ : Perm (Fin n)) {v : Fin n → Fˣ} (hv : v ∈ prodOneUnits F n) :
    v ∘ σ ∈ prodOneUnits F n := by
  rw [mem_prodOneUnits] at hv ⊢
  rw [← hv]
  exact Equiv.prod_comp σ v

variable (F n)

@[expose] def diagSLHom : prodOneUnits F n →* SpecialLinearGroup (Fin n) F where
  toFun v := ⟨diagonal fun j => ((v : Fin n → Fˣ) j : F), by
    rw [det_diagonal, ← Units.coe_prod, (mem_prodOneUnits.mp v.2), Units.val_one]⟩
  map_one' := Subtype.ext (by
    change (diagonal fun _ => ((1 : Fˣ) : F)) = 1
    simp)
  map_mul' v w := Subtype.ext (by
    change (diagonal fun j => (((v * w : prodOneUnits F n) : Fin n → Fˣ) j : F)) =
      (diagonal fun j => ((v : Fin n → Fˣ) j : F)) * diagonal fun j => ((w : Fin n → Fˣ) j : F)
    rw [diagonal_mul_diagonal]
    rfl)


variable {F n}

theorem coe_diagSLHom (v : prodOneUnits F n) :
    (diagSLHom F n v : Matrix (Fin n) (Fin n) F) = diagonal fun j => ((v : Fin n → Fˣ) j : F) :=
  rfl


theorem signedPermutation_mul_diagSLHom (a b : Fin n) (v : prodOneUnits F n) :
    signedPermutation n F (swap a b) * diagSLHom F n v =
      diagSLHom F n ⟨v ∘ swap a b, comp_mem_prodOneUnits _ v.2⟩ *
        signedPermutation n F (swap a b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagSLHom,
    coe_diagSLHom, coe_signedPermutation, signedPermMatrix_mul_diagonal, swap_inv]
  rfl


theorem torusVec_mem_prodOneUnits (ζ : Fˣ) (i d : Fin n) : torusVec ζ i d ∈ prodOneUnits F n :=
  mem_prodOneUnits.mpr (prod_torusVec ζ i d)


end Linear

section Unitary

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {n : ℕ}

variable (n) in
@[expose] noncomputable def normOneProdOne : Subgroup (Fin n → Kˣ) :=
  prodOneUnits K n ⊓ Subgroup.pi Set.univ fun _ => (Units.map h.normHom).ker

theorem mem_normOneProdOne {v : Fin n → Kˣ} :
    v ∈ normOneProdOne h n ↔ ∏ j, v j = 1 ∧ ∀ j, h.norm (v j : K) = 1 := by
  rw [normOneProdOne, mem_inf, mem_prodOneUnits, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, h.mem_ker_normUnits]

theorem comp_mem_normOneProdOne (σ : Perm (Fin n)) {v : Fin n → Kˣ}
    (hv : v ∈ normOneProdOne h n) : v ∘ σ ∈ normOneProdOne h n := by
  rw [mem_normOneProdOne] at hv ⊢
  exact ⟨by rw [← hv.1]; exact Equiv.prod_comp σ v, fun j => hv.2 (σ j)⟩

theorem prodOne_of_mem_normOneProdOne {v : Fin n → Kˣ} (hv : v ∈ normOneProdOne h n) :
    v ∈ prodOneUnits K n :=
  (mem_inf.mp hv).1

theorem toGL_mem_unitarySU {A : SpecialLinearGroup (Fin n) K}
    (hA : (((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K)) = 1) :
    Matrix.SpecialLinearGroup.toGL A ∈ unitarySU ℓ f K n := by
  rw [mem_unitarySU_iff h, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  exact ⟨A.2, hA⟩

theorem diagSLHom_mem_unitarySU (v : normOneProdOne h n) :
    Matrix.SpecialLinearGroup.toGL (diagSLHom K n ⟨v, prodOne_of_mem_normOneProdOne h v.2⟩) ∈
      unitarySU ℓ f K n := by
  refine toGL_mem_unitarySU h ?_
  rw [coe_diagSLHom, diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext j
  rw [mul_comm]
  exact ((mem_normOneProdOne h).mp v.2).2 j

theorem signedPermMatrix_map_bar (w : Perm (Fin n)) :
    (signedPermMatrix n K w).map h.bar = signedPermMatrix n K w := by
  ext a b
  simp only [Matrix.map_apply, signedPermMatrix_apply]
  split_ifs <;> simp

include h in
theorem signedPermutation_mem_unitarySU (w : Perm (Fin n)) :
    Matrix.SpecialLinearGroup.toGL (signedPermutation n K w) ∈ unitarySU ℓ f K n := by
  refine toGL_mem_unitarySU h ?_
  rw [coe_signedPermutation, signedPermMatrix_map_bar, transpose_signedPermMatrix_mul_self]

variable (n)

@[expose] noncomputable def unitaryDiagHom : normOneProdOne h n →* unitarySU ℓ f K n where
  toFun v := ⟨_, diagSLHom_mem_unitarySU h v⟩
  map_one' := Subtype.ext (by
    change Matrix.SpecialLinearGroup.toGL (diagSLHom K n 1) = 1
    rw [map_one, map_one])
  map_mul' v w := Subtype.ext (by
    change Matrix.SpecialLinearGroup.toGL (diagSLHom K n
      (⟨v, prodOne_of_mem_normOneProdOne h v.2⟩ * ⟨w, prodOne_of_mem_normOneProdOne h w.2⟩)) = _
    rw [map_mul, map_mul]
    rfl)

@[expose] noncomputable def unitaryDelta : normOneProdOne h n →* unitaryPSU h n :=
  (unitaryProj h n).comp (unitaryDiagHom h n)

@[expose] noncomputable def unitarySignedSwap (a b : Fin n) : unitarySU ℓ f K n :=
  ⟨_, signedPermutation_mem_unitarySU h (swap a b)⟩

@[expose] noncomputable def unitaryWeyl (a b : Fin n) : unitaryPSU h n :=
  unitaryProj h n (unitarySignedSwap h n a b)

variable {n}

theorem coe_unitaryDiagHom (v : normOneProdOne h n) :
    ((unitaryDiagHom h n v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun j => ((v : Fin n → Kˣ) j : K) :=
  rfl

theorem unitaryDelta_eq_one {v : normOneProdOne h n} (hv : unitaryDelta h n v = 1) (j k : Fin n) :
    (v : Fin n → Kˣ) j = (v : Fin n → Kˣ) k := by
  have hv' : unitaryDiagHom h n v ∈ unitaryScalars h n := by
    rw [← ker_unitaryProj, MonoidHom.mem_ker]
    exact hv
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp hv'
  have h1 : ∀ x : Fin n, ((v : Fin n → Kˣ) x : K) = c := by
    intro x
    have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) x x) hc
    simp only [coe_unitaryDiagHom, diagonal_apply_eq, GeneralLinearGroup.coe_scalar,
      scalar_apply] at this
    exact this
  exact Units.ext ((h1 j).trans (h1 k).symm)

theorem unitaryWeyl_conj (a b : Fin n) (v : normOneProdOne h n) :
    unitaryWeyl h n a b * unitaryDelta h n v * (unitaryWeyl h n a b)⁻¹ =
      unitaryDelta h n ⟨v ∘ swap a b, comp_mem_normOneProdOne h _ v.2⟩ := by
  have key : unitarySignedSwap h n a b * unitaryDiagHom h n v =
      unitaryDiagHom h n ⟨v ∘ swap a b, comp_mem_normOneProdOne h _ v.2⟩ *
        unitarySignedSwap h n a b := by
    apply Subtype.ext
    have := congrArg Matrix.SpecialLinearGroup.toGL
      (signedPermutation_mul_diagSLHom (F := K) a b ⟨v, prodOne_of_mem_normOneProdOne h v.2⟩)
    rw [map_mul, map_mul] at this
    exact this
  rw [unitaryWeyl, unitaryDelta, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv,
    ← map_mul, ← map_mul, key, mul_inv_cancel_right]


theorem torusVec_mem_normOneProdOne {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1) (i d : Fin n) :
    torusVec ζ i d ∈ normOneProdOne h n := by
  refine (mem_normOneProdOne h).mpr ⟨prod_torusVec ζ i d, fun j => ?_⟩
  have hinv : h.norm ((ζ⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, CFSG.ClassicalGroups.UnitaryFlag.norm_inv_eq h, hζ, inv_one]
  have hn1 : h.norm ((1 : Kˣ) : K) = 1 := by simp [UnitaryFieldData.norm]
  have e1 : h.norm (((if j = i then ζ else 1 : Kˣ)) : K) = 1 := by
    split_ifs
    · exact hζ
    · exact hn1
  have e2 : h.norm (((if j = d then ζ⁻¹ else 1 : Kˣ)) : K) = 1 := by
    split_ifs
    · exact hinv
    · exact hn1
  rw [torusVec_apply, Units.val_mul, CFSG.ClassicalGroups.UnitaryFlag.norm_mul_eq h, e1, e2,
    one_mul]

variable (n) in
@[expose] noncomputable def unitaryTorusClass {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1) (i d : Fin n) :
    unitaryPSU h n :=
  unitaryDelta h n ⟨torusVec ζ i d, torusVec_mem_normOneProdOne h hζ i d⟩

end Unitary

end CFSG.LocalAnalysis.GorensteinLyons
