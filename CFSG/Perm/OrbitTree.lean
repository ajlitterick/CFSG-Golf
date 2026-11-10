module

public import Mathlib.GroupTheory.Index
import Mathlib.Order.Interval.Set.Nat

public section

namespace CFSG.Perm

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def treeWord (par lab : ℕ → ℕ) (ℓ : ℕ → G) (i : ℕ) : G :=
  if _h : 0 < i ∧ par i < i then ℓ (lab i) * treeWord par lab ℓ (par i) else 1
termination_by i

@[simp] theorem treeWord_zero (par lab : ℕ → ℕ) (ℓ : ℕ → G) : treeWord par lab ℓ 0 = 1 := by
  rw [treeWord.eq_def]; simp

theorem treeWord_of_pos {par : ℕ → ℕ} (lab : ℕ → ℕ) (ℓ : ℕ → G) {i : ℕ} (hi : 0 < i)
    (hpar : par i < i) : treeWord par lab ℓ i = ℓ (lab i) * treeWord par lab ℓ (par i) := by
  rw [treeWord.eq_def par lab ℓ i, dite_eq_left ⟨hi, hpar⟩]

theorem smul_mem_of_finite_of_mem_closure {S : Set G} {F : Set X} (hF : F.Finite)
    (hSF : ∀ s ∈ S, ∀ x ∈ F, s • x ∈ F) {g : G} (hg : g ∈ Subgroup.closure S) {x : X}
    (hx : x ∈ F) : g • x ∈ F := by
  induction hg using Subgroup.closure_induction generalizing x with
  | mem s hs => exact hSF s hs x hx
  | one => rwa [one_smul]
  | mul a b _ _ ha hb => rw [mul_smul]; exact ha (hb hx)
  | inv a _ ha =>
    have hbij := (hF.injOn_iff_bijOn_of_mapsTo (f := (a • ·)) fun y hy => ha hy).1
      fun y _ z _ h => smul_left_cancel a h
    obtain ⟨y, hy, rfl⟩ := hbij.surjOn hx
    rwa [inv_smul_smul]

section Points

variable {S : Set G} {n : ℕ} {P : ℕ → X}

private theorem ncard_image_lt (hPinj : ∀ i < n, ∀ j < n, P i = P j → i = j) :
    (P '' {i | i < n}).ncard = n := by
  rw [Set.InjOn.ncard_image (s := {i | i < n}) fun i hi j hj h => hPinj i hi j hj h]
  exact Set.ncard_Iio_nat n

theorem exists_eq_smul_of_mem_closure (hclosed : ∀ i < n, ∀ s ∈ S, ∃ j < n, P j = s • P i)
    {g : G} (hg : g ∈ Subgroup.closure S) {i : ℕ} (hi : i < n) : ∃ j < n, P j = g • P i := by
  obtain ⟨j, hj, e⟩ := smul_mem_of_finite_of_mem_closure ((Set.finite_lt_nat n).image P)
    (by
      rintro s hs _ ⟨k, hk, rfl⟩
      obtain ⟨j, hj, e⟩ := hclosed k hk s hs
      exact ⟨j, hj, e⟩) hg ⟨i, hi, rfl⟩
  exact ⟨j, hj, e⟩

theorem schreier_mem_of_mem_closure (hPinj : ∀ i < n, ∀ j < n, P i = P j → i = j)
    (hclosed : ∀ i < n, ∀ s ∈ S, ∃ j < n, P j = s • P i) {τ : ℕ → G} {K : Subgroup G}
    (hK : ∀ i < n, ∀ s ∈ S, ∀ j < n, P j = s • P i → (τ j)⁻¹ * s * τ i ∈ K)
    {g : G} (hg : g ∈ Subgroup.closure S) {i j : ℕ} (hi : i < n) (hj : j < n)
    (hgij : P j = g • P i) : (τ j)⁻¹ * g * τ i ∈ K := by
  induction hg using Subgroup.closure_induction generalizing i j with
  | mem s hs => exact hK i hi s hs j hj hgij
  | one =>
    rw [hPinj j hj i hi (by rw [hgij, one_smul]), mul_one, inv_mul_cancel]
    exact K.one_mem
  | mul a b _ hb iha ihb =>
    obtain ⟨k, hk, hkb⟩ := exists_eq_smul_of_mem_closure hclosed hb hi
    have := K.mul_mem (iha hk hj (by rw [hgij, hkb, mul_smul])) (ihb hi hk hkb)
    simpa only [mul_assoc, mul_inv_cancel_left] using this
  | inv a _ iha =>
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using
      K.inv_mem (iha hj hi (by rw [hgij, smul_inv_smul]))

theorem orbit_closure_eq_image (hn : 0 < n)
    (hclosed : ∀ i < n, ∀ s ∈ S, ∃ j < n, P j = s • P i) {τ : ℕ → G}
    (hτS : ∀ i < n, τ i ∈ Subgroup.closure S) (hτ : ∀ i < n, τ i • P 0 = P i) :
    MulAction.orbit (Subgroup.closure S) (P 0) = P '' {i | i < n} := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨j, hj, e⟩ := exists_eq_smul_of_mem_closure hclosed g.2 hn
    exact ⟨j, hj, e⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨τ i, hτS i hi⟩, hτ i hi⟩

theorem card_closure_eq_mul (hn : 0 < n) (hPinj : ∀ i < n, ∀ j < n, P i = P j → i = j)
    (hclosed : ∀ i < n, ∀ s ∈ S, ∃ j < n, P j = s • P i) {τ : ℕ → G} (hτ0 : τ 0 = 1)
    (hτS : ∀ i < n, τ i ∈ Subgroup.closure S) (hτ : ∀ i < n, τ i • P 0 = P i) {K : Subgroup G}
    (hKS : K ≤ Subgroup.closure S) (hKP : K ≤ MulAction.stabilizer G (P 0))
    (hK : ∀ i < n, ∀ s ∈ S, ∀ j < n, P j = s • P i → (τ j)⁻¹ * s * τ i ∈ K) :
    Nat.card (Subgroup.closure S) = n * Nat.card K := by
  have hstab : MulAction.stabilizer (Subgroup.closure S) (P 0) =
      K.subgroupOf (Subgroup.closure S) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    refine ⟨fun hg => ?_, fun hg => hKP hg⟩
    have := schreier_mem_of_mem_closure hPinj hclosed hK g.2 hn hn hg.symm
    rwa [hτ0, inv_one, one_mul, mul_one] at this
  rw [← Subgroup.index_mul_card (MulAction.stabilizer (Subgroup.closure S) (P 0)),
    MulAction.index_stabilizer, orbit_closure_eq_image hn hclosed hτS hτ, ncard_image_lt hPinj,
    hstab, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKS).toEquiv]

end Points

section Tree

variable {S : Set G} {n : ℕ} {P : ℕ → X} {par lab : ℕ → ℕ} {ℓ : ℕ → G}

theorem treeWord_smul (hpar : ∀ i, 0 < i → i < n → par i < i)
    (htree : ∀ i, 0 < i → i < n → P i = ℓ (lab i) • P (par i)) {i : ℕ} (hi : i < n) :
    treeWord par lab ℓ i • P 0 = P i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [treeWord_zero, one_smul]
    · have hp := hpar i hi0 hi
      rw [treeWord_of_pos lab ℓ hi0 hp, mul_smul, ih _ hp (hp.trans hi), htree i hi0 hi]

theorem treeWord_mem {H : Subgroup G} (hpar : ∀ i, 0 < i → i < n → par i < i)
    (hℓ : ∀ i, 0 < i → i < n → ℓ (lab i) ∈ H) {i : ℕ} (hi : i < n) :
    treeWord par lab ℓ i ∈ H := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [treeWord_zero]
      exact H.one_mem
    · have hp := hpar i hi0 hi
      rw [treeWord_of_pos lab ℓ hi0 hp]
      exact H.mul_mem (hℓ i hi0 hi) (ih _ hp (hp.trans hi))

theorem orbitTree_orbit_eq (hS : Subgroup.closure S = ⊤) (hn : 0 < n)
    (hclosed : ∀ i < n, ∀ s ∈ S, ∃ j < n, P j = s • P i)
    (hpar : ∀ i, 0 < i → i < n → par i < i)
    (htree : ∀ i, 0 < i → i < n → P i = ℓ (lab i) • P (par i)) :
    MulAction.orbit G (P 0) = P '' {i | i < n} := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨j, hj, e⟩ := exists_eq_smul_of_mem_closure hclosed (hS ▸ Subgroup.mem_top g) hn
    exact ⟨j, hj, e⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨treeWord par lab ℓ i, treeWord_smul hpar htree hi⟩

theorem orbitTree_card_orbit (hS : Subgroup.closure S = ⊤) (hn : 0 < n)
    (hPinj : ∀ i < n, ∀ j < n, P i = P j → i = j)
    (hclosed : ∀ i < n, ∀ s ∈ S, ∃ j < n, P j = s • P i)
    (hpar : ∀ i, 0 < i → i < n → par i < i)
    (htree : ∀ i, 0 < i → i < n → P i = ℓ (lab i) • P (par i)) :
    Nat.card (MulAction.orbit G (P 0)) = n := by
  rw [orbitTree_orbit_eq hS hn hclosed hpar htree, Nat.card_coe_set_eq, ncard_image_lt hPinj]

end Tree

theorem orbitTree_schreier (S : Set G) (hS : Subgroup.closure S = ⊤) (n : ℕ) (hn : 0 < n)
    (P : ℕ → X) (hPinj : ∀ i < n, ∀ j < n, P i = P j → i = j)
    (hclosed : ∀ i < n, ∀ s ∈ S, ∃ j < n, P j = s • P i)
    (par lab : ℕ → ℕ) (ℓ : ℕ → G)
    (hpar : ∀ i, 0 < i → i < n → par i < i)
    (htree : ∀ i, 0 < i → i < n → P i = ℓ (lab i) • P (par i))
    (K : Subgroup G)
    (hK : ∀ i < n, ∀ s ∈ S, ∀ j < n, P j = s • P i →
      (treeWord par lab ℓ j)⁻¹ * s * treeWord par lab ℓ i ∈ K) :
    MulAction.stabilizer G (P 0) ≤ K ∧
      Nat.card G = n * Nat.card (MulAction.stabilizer G (P 0)) := by
  refine ⟨fun g hg => ?_, ?_⟩
  · have := schreier_mem_of_mem_closure hPinj hclosed hK (hS ▸ Subgroup.mem_top g) hn hn
      (MulAction.mem_stabilizer_iff.1 hg).symm
    rwa [treeWord_zero, inv_one, one_mul, mul_one] at this
  · rw [← Subgroup.index_mul_card (MulAction.stabilizer G (P 0)), MulAction.index_stabilizer,
      ← Nat.card_coe_set_eq, orbitTree_card_orbit hS hn hPinj hclosed hpar htree]

section Skip


end Skip


section Edges


end Edges

end CFSG.Perm
