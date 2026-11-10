module

public import CFSG.YGroups.Y443.CentralProjection
public import CFSG.YGroups.DCE.B433Maximal

public section

namespace CFSG.YGroups.Y443Edge

open CFSG.Open (MonsterY443Derived)
open CFSG.YGroups.DCE.B433 (psi psi_range_maximal)

@[expose] noncomputable def qc : Q343 := Q343.π (Y343.F 1 2 3)

theorem y443Q343Hom_gen
    {c : ℕ} (hc : c < 11) :
    y443Q343Hom (Q343.π (yGen 3 4 3 c)) = y443Tl (shiftAt 3 c) := y443Q343Hom_π hc

theorem y443Q343Hom_qc :
    y443Q343Hom qc = y443C := by
  have e : ∀ c < 11, y443Q343Hom (Q343.π (yGen 3 4 3 c)) = y443Tl (shiftAt 3 c) :=
    fun c hc => y443Q343Hom_gen hc
  have hF : Y343.F 1 2 3 = (yGen 3 4 3 0 * yGen 3 4 3 1 * yGen 3 4 3 2 * yGen 3 4 3 3 *
      yGen 3 4 3 4 * yGen 3 4 3 5 * yGen 3 4 3 8) ^ 9 := rfl
  have hF0 : y443F0 = (y443Gen 0 * y443Gen 1 * y443Gen 2 * y443Gen 3 * y443Gen 5 * y443Gen 6 *
      y443Gen 9) ^ 9 := rfl
  rw [← y443Pi_F0, qc, hF, hF0]
  simp only [map_pow, map_mul]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
    e 4 (by norm_num), e 5 (by norm_num), e 8 (by norm_num), y443Pi_gen, y443Pi_gen, y443Pi_gen,
    y443Pi_gen, y443Pi_gen, y443Pi_gen, y443Pi_gen]
  have h4 : shiftAt 3 4 = 5 := by decide
  have h5 : shiftAt 3 5 = 6 := by decide
  have h8 : shiftAt 3 8 = 9 := by decide
  have h0 : shiftAt 3 0 = 0 := by decide
  have h1 : shiftAt 3 1 = 1 := by decide
  have h2 : shiftAt 3 2 = 2 := by decide
  have h3 : shiftAt 3 3 = 3 := by decide
  rw [h0, h1, h2, h3, h4, h5, h8]

@[expose] noncomputable def beta :
    Q343 →* B433 :=
  R433.toB433.comp Q343EquivR433.toMonoidHom

theorem beta_surjective :
    Function.Surjective beta := by
  intro b
  obtain ⟨r, rfl⟩ := R433.toB433_surjective b
  refine ⟨Q343EquivR433.symm r, ?_⟩
  rw [beta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem Q343EquivR433_qc :
    Q343EquivR433 qc = R433.c312 := by
  rw [qc, Q343EquivR433_π, cyc343Equiv_F123]
  rfl

theorem ker_beta :
    beta.ker = Subgroup.zpowers qc := by
  ext q
  rw [MonoidHom.mem_ker, beta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker,
    R433.ker_toB433, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, Q343EquivR433.injective ?_⟩
    rw [map_zpow, Q343EquivR433_qc, hn]
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [map_zpow, Q343EquivR433_qc]⟩

theorem qc_mul_self :
    qc * qc = 1 := by
  apply Q343EquivR433.injective
  rw [map_mul, Q343EquivR433_qc, R433.c312_mul_self, map_one]

theorem qc_comm
    (q : Q343) : q * qc = qc * q := by
  apply Q343EquivR433.injective
  rw [map_mul, map_mul, Q343EquivR433_qc]
  exact (Subgroup.mem_center_iff.1 R433.c312_mem_center _)


@[expose] noncomputable def Kq : Subgroup Q343 :=
  Subgroup.closure ((fun c => Q343.π (yGen 3 4 3 c)) '' {c | c < 11 ∧ c ≠ 3})


theorem beta_gen
    {c : ℕ} (hc : c < 11) :
    beta (Q343.π (yGen 3 4 3 c)) = DCE.B433.qB (yGen 4 3 3 (cyc343Letter c)) := by
  rw [beta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Q343EquivR433_π,
    cyc343Equiv_yGen hc, R433.toB433_π]
  rfl


variable {G : Type*} [Group G] (f : MonsterY443Derived →* G)

@[expose] noncomputable def rho :
    Q343 →* G := f.comp y443Q343Hom

theorem range_rho :
    (rho f).range = y443H.map f := by
  rw [rho, MonoidHom.range_comp, y443Q343Hom_range]

theorem rho_injective
    (hN : Q343N ≤ Nat.card (y443H.map f)) : Function.Injective (rho f) := by
  have := Q343_finite_card_le.1
  have hle : Nat.card Q343 ≤ Nat.card (rho f).range := by
    rw [range_rho]
    exact Q343_finite_card_le.2.trans hN
  have hb := (rho f).rangeRestrict_surjective.bijective_of_nat_card_le hle
  intro a b hab
  apply hb.1
  exact Subtype.ext hab

theorem card_B433_ge
    (hN : Q343N ≤ Nat.card (y443H.map f)) :
    4154781481226426191177580544000000 ≤ Nat.card B433 := by
  have := Q343_finite_card_le.1
  have h1 : Q343N ≤ Nat.card Q343 := by
    have := Nat.card_le_card_of_surjective _ (rho f).rangeRestrict_surjective
    rw [range_rho] at this
    exact hN.trans this
  have h2 : Nat.card Q343 = Nat.card R433 := Nat.card_congr Q343EquivR433.toEquiv
  have h3 := R433.card_eq_mul
  have h4 : Nat.card (Subgroup.zpowers R433.c312) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) R433.c312_pow_two
  have hQ : Q343N = 2 * 4154781481226426191177580544000000 := by unfold Q343N; norm_num
  rw [h2, h3, hQ] at h1
  have := Nat.mul_le_mul_right (Nat.card B433) h4
  omega

@[expose] noncomputable def S :
    Subgroup Q343 :=
  (y443H.map f ⊓ (y443H.map f).comap (MulAut.conj (f y443X)).toMonoidHom).comap (rho f)

theorem mem_S
    {q : Q343} :
    q ∈ S f ↔ rho f q ∈ y443H.map f ∧ f y443X * rho f q * f y443X ∈ y443H.map f := by
  have hx : (f y443X)⁻¹ = f y443X := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right y443X_mul_self]
  simp only [S, Subgroup.mem_comap, Subgroup.mem_inf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, hx]


theorem fC_comm
    {h : G} (hh : h ∈ y443H.map f) : h * f y443C = f y443C * h := by
  obtain ⟨hc, hcen⟩ := (y443_terminal_central_map f).1
  have := Subgroup.mem_center_iff.1 hcen ⟨h, hh⟩
  exact congrArg Subtype.val this

theorem xcx_not_mem
    (hd : f y443C * (f y443X * f y443C * f y443X) ≠ (f y443X * f y443C * f y443X) * f y443C) :
    f y443X * f y443C * f y443X ∉ y443H.map f := fun h => hd (fC_comm f h).symm

theorem x_not_mem
    (hd : f y443C * (f y443X * f y443C * f y443X) ≠ (f y443X * f y443C * f y443X) * f y443C) :
    f y443X ∉ y443H.map f := by
  intro hx
  apply xcx_not_mem f hd
  have hc : f y443C ∈ y443H.map f := ⟨y443C, y443C_mem_H, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hc) hx


theorem zpowers_qc_le_center :
    Subgroup.zpowers qc ≤ Subgroup.center Q343 :=
  Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 fun g => qc_comm g)

instance zpowers_qc_normal :
    (Subgroup.zpowers qc).Normal :=
  Subgroup.normal_of_le_center zpowers_qc_le_center

theorem mem_sup_zpowers_qc
    {A : Subgroup Q343} {g : Q343} (hg : g ∈ A ⊔ Subgroup.zpowers qc) :
    g ∈ A ∨ g * qc ∈ A := by
  have hg' : g ∈ (↑(A ⊔ Subgroup.zpowers qc) : Set Q343) := hg
  rw [Subgroup.mul_normal] at hg'
  obtain ⟨a, ha, z, hz, rfl⟩ := Set.mem_mul.1 hg'
  rcases mem_zpowers_involution qc_mul_self hz with rfl | rfl
  · left; rwa [mul_one]
  · right; rwa [mul_assoc, qc_mul_self, mul_one]


theorem injOn_H
    (hN : Q343N ≤ Nat.card (y443H.map f)) : Set.InjOn f y443H := by
  intro a ha b hb hab
  rw [SetLike.mem_coe, ← y443Q343Hom_range] at ha hb
  obtain ⟨q, rfl⟩ := ha
  obtain ⟨q', rfl⟩ := hb
  have : q = q' := rho_injective f hN hab
  rw [this]


end CFSG.YGroups.Y443Edge
