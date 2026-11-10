module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHsylBasic
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
import CFSG.LocalAnalysis.SeitzReduction.F4PilotKernel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusLayer

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace mem_omegaGroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section General

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b a₂ b₂ a₃ b₃ : Fin d}

theorem exists_card_eq_two_pow [Finite K] [CharP K 2] : ∃ f : ℕ, Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem IsHypCoord.pairTorusOf_le_centralizer_pairPerpOf (h : IsHypCoord Q a b) :
    pairTorusOf Q a b ≤ centralizer (pairPerpOf Q a b : Set (matrixProjectiveDerived Q)) := by
  rintro _ ⟨y, ⟨c, hc⟩, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change (z : (Fin d → K) ≃ₗ[K] (Fin d → K)) * y = y * z
  have hc1 : torusLin a b c = (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) := hc
  rw [← hc1]
  exact h.commute_torusLin_of_mem_stabSub (Subgroup.commutator_le_self _ z.2) hz c

theorem IsHypCoord.linearEquiv_ext (h : IsHypCoord Q a b) {g g' : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (ha : g (Pi.single a 1) = g' (Pi.single a 1)) (hb : g (Pi.single b 1) = g' (Pi.single b 1))
    (hU : ∀ x ∈ perpSub K a b, g x = g' x) : g = g' := by
  apply LinearEquiv.ext
  intro x
  rw [eq_add_perpPart a b x, map_add, map_add, map_smul, map_smul, ha, hb,
    hU _ (perpPart_mem h.ne x), map_add, map_add, map_smul, map_smul]

variable [Finite K] [CharP K 2]

theorem exists_mem_pairTorusOf_eq_conj (hQ : (polarBilin Q).Nondegenerate)
    (h : IsHypCoord Q a b) (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃)
    (d₂ : PairDisjoint a b a₂ b₂) (d₃ : PairDisjoint a b a₃ b₃) (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃)
    (hq : 3 ≤ Nat.card K) {β : MulAut (matrixProjectiveDerived Q)}
    (hβE : β ∈ matrixProjectiveImage Q) (hX : ∀ x ∈ pairTorusOf Q a b, β x = x)
    (hD : ∀ x ∈ pairPerpOf Q a b, β x = x) :
    ∃ x ∈ pairTorusOf Q a b, β = MulAut.conj x := by
  have hT := exists_threeSingular_of_isHypCoord h h₂ h₃ d₂ d₃ d₂₃
  have hQ' := h.exists_ne_zero
  obtain ⟨g, rfl⟩ := hβE
  obtain ⟨c₀, hc₀⟩ := exists_units_ne_one (K := K) hq
  have hu₂ : (Pi.single a₂ 1 : Fin d → K) ∈ perpSub K a b ∧
      (Pi.single b₂ 1 : Fin d → K) ∈ perpSub K a b := h₂.hypPair_mem_perpSub d₂
  have hDcomm : ∀ u ∈ perpSub K a b, ∀ w ∈ perpSub K a b, ∀ x,
      simMap g (eichler Q u w x) = eichler Q u w (simMap g x) := by
    intro u hu w hw x
    exact commute_of_kappa_projHom_eq hQ' g
      (E := ⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩)
      (hD _ ⟨⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩, h.eichler_mem_stabSub hu hw,
        rfl⟩) x
  have hXcomm : ∀ x, simMap g (torusLin a b c₀ x) = torusLin a b c₀ (simMap g x) :=
    commute_of_kappa_projHom_eq hQ' g (E := ⟨torusLin a b c₀, h.torusLin_mem_orthDerived c₀⟩)
      (hX _ ⟨_, ⟨c₀, rfl⟩, rfl⟩)
  obtain ⟨-, γ, α, hγ0, hφ⟩ := eq_smul_torusLin_of_commute hQ h h₂ h₃ d₂ d₃ d₂₃
    (Units.ne_zero (multiplier Q g)) (simMap_smul g) (map_simMap g)
    (fun w hw _ x => hDcomm _ hu₂.1 w hw x) (fun w hw _ x => hDcomm _ hu₂.2 w hw x) hc₀ hXcomm
  exact ⟨projHom Q ⟨torusLin a b α, h.torusLin_mem_orthDerived α⟩, ⟨_, ⟨α, rfl⟩, rfl⟩,
    kappa_eq_conj_of_eq_smul g _ hγ0 hφ⟩

theorem eq_one_of_two_pow_fix_pairTorusOf (hQ : (polarBilin Q).Nondegenerate)
    (h : IsHypCoord Q a b) (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃)
    (d₂ : PairDisjoint a b a₂ b₂) (d₃ : PairDisjoint a b a₃ b₃) (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃)
    (hq : 3 ≤ Nat.card K) {β : MulAut (matrixProjectiveDerived Q)}
    (hβE : β ∈ matrixProjectiveImage Q) {m : ℕ} (hβ : β ^ 2 ^ m = 1)
    (hX : ∀ x ∈ pairTorusOf Q a b, β x = x) (hD : ∀ x ∈ pairPerpOf Q a b, β x = x) : β = 1 := by
  obtain ⟨x, hx, rfl⟩ := exists_mem_pairTorusOf_eq_conj hQ h h₂ h₃ d₂ d₃ d₂₃ hq hβE hX hD
  obtain ⟨f, hK⟩ := exists_card_eq_two_pow (K := K)
  have hodd := odd_card_pairTorusOf h hK
  have hx1 : x ^ Nat.card (pairTorusOf Q a b) = 1 := by
    have h1 := pow_card_eq_one' (G := pairTorusOf Q a b) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val h1
  have h1 : MulAut.conj x ^ Nat.card (pairTorusOf Q a b) = 1 := by rw [← map_pow, hx1, map_one]
  have hcop : Nat.Coprime (2 ^ m) (Nat.card (pairTorusOf Q a b)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hβ)
    (orderOf_dvd_of_pow_eq_one h1))


end General

section Coordinates

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv minusIndexEquiv coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadPlus
    regular_coordinateQuadMinus)

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem exists_mem_pairTorus_eq_conj (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 5 ≤ n) (k : Fin n)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (hX : ∀ x ∈ pairTorus (K := K) k, β x = x) (hD : ∀ x ∈ pairPerp (K := K) k, β x = x) :
    ∃ x ∈ pairTorus (K := K) k, β = MulAut.conj x := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by omega : 3 ≤ n) k
  refine exists_mem_pairTorusOf_eq_conj (regular_coordinateQuadPlus n K (by omega)).1
    (isHypCoord_coordinateQuadPlus k) (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) (pairDisjoint_plus hik.symm) (pairDisjoint_plus hjk.symm)
    (pairDisjoint_plus hij) (by omega) ?_ hX hD
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn]
  exact Subgroup.mem_top β

theorem eq_one_of_two_pow_fix_pairTorus (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 5 ≤ n) (k : Fin n)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} {m : ℕ} (hβ : β ^ 2 ^ m = 1)
    (hX : ∀ x ∈ pairTorus (K := K) k, β x = x) (hD : ∀ x ∈ pairPerp (K := K) k, β x = x) :
    β = 1 := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by omega : 3 ≤ n) k
  refine eq_one_of_two_pow_fix_pairTorusOf (regular_coordinateQuadPlus n K (by omega)).1
    (isHypCoord_coordinateQuadPlus k) (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) (pairDisjoint_plus hik.symm) (pairDisjoint_plus hjk.symm)
    (pairDisjoint_plus hij) (by omega) ?_ hβ hX hD
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn]
  exact Subgroup.mem_top β

theorem exists_mem_minusPairTorus_eq_conj (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    {β : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))}
    (hX : ∀ x ∈ minusPairTorus (K := K) (one_le_of_four_le hn) b c k, β x = x)
    (hD : ∀ x ∈ minusPairPerp (K := K) (one_le_of_four_le hn) b c k, β x = x) :
    ∃ x ∈ minusPairTorus (K := K) (one_le_of_four_le hn) b c k, β = MulAut.conj x := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by omega : 3 ≤ n - 1) k
  refine exists_mem_pairTorusOf_eq_conj (regular_coordinateQuadMinus n K b c hn hirr).1
    (isHypCoord_coordinateQuadMinus _ b c k) (isHypCoord_coordinateQuadMinus _ b c i)
    (isHypCoord_coordinateQuadMinus _ b c j) (pairDisjoint_minus _ hik.symm)
    (pairDisjoint_minus _ hjk.symm) (pairDisjoint_minus _ hij) (by omega) ?_ hX hD
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr]
  exact Subgroup.mem_top β

theorem eq_one_of_two_pow_fix_minusPairTorus (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    {β : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))} {m : ℕ}
    (hβ : β ^ 2 ^ m = 1) (hX : ∀ x ∈ minusPairTorus (K := K) (one_le_of_four_le hn) b c k, β x = x)
    (hD : ∀ x ∈ minusPairPerp (K := K) (one_le_of_four_le hn) b c k, β x = x) : β = 1 := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by omega : 3 ≤ n - 1) k
  refine eq_one_of_two_pow_fix_pairTorusOf (regular_coordinateQuadMinus n K b c hn hirr).1
    (isHypCoord_coordinateQuadMinus _ b c k) (isHypCoord_coordinateQuadMinus _ b c i)
    (isHypCoord_coordinateQuadMinus _ b c j) (pairDisjoint_minus _ hik.symm)
    (pairDisjoint_minus _ hjk.symm) (pairDisjoint_minus _ hij) (by omega) ?_ hβ hX hD
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr]
  exact Subgroup.mem_top β

end Coordinates

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {C : Type*} [Group C]

theorem eq_one_of_fix_map_of_mulEquiv (e : L ≃* C) {XC DC : Subgroup C}
    (hC : ∀ β : MulAut C, (∀ x ∈ XC, β x = x) → (∀ x ∈ DC, β x = x) →
      ∀ m : ℕ, β ^ 2 ^ m = 1 → β = 1) :
    ∀ β : MulAut L,
      (∀ a : L, (a : G) ∈ (XC.map e.symm.toMonoidHom).map L.subtype → β a = a) →
      (∀ a : L, (a : G) ∈ (DC.map e.symm.toMonoidHom).map L.subtype → β a = a) →
      ∀ m : ℕ, β ^ 2 ^ m = 1 → β = 1 := by
  intro β hβX hβD m hβm
  have hmem : ∀ {YC : Subgroup C} {x : C}, x ∈ YC →
      ((e.symm x : L) : G) ∈ (YC.map e.symm.toMonoidHom).map L.subtype :=
    fun {YC} {x} hx => ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
  have key : MulAut.congr e β = 1 := by
    refine hC _ (fun x hx => ?_) (fun x hx => ?_) m ?_
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβX _ (hmem hx),
        MulEquiv.apply_symm_apply]
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβD _ (hmem hx),
        MulEquiv.apply_symm_apply]
    · rw [← map_pow, hβm, map_one]
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

theorem mem_of_odd_of_commute_of_mulEquiv [Finite C] (e : L ≃* C) {XC DC : Subgroup C}
    (hodd : Odd (Nat.card XC))
    (hC : ∀ β : MulAut C, (∀ x ∈ XC, β x = x) → (∀ x ∈ DC, β x = x) →
      ∃ x ∈ XC, β = MulAut.conj x)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∀ c ∈ centralizer (((XC.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) ⊓
        centralizer (((DC.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G),
      Odd (orderOf c) → c ∈ (XC.map e.symm.toMonoidHom).map L.subtype := by
  intro c ⟨⟨hcX, hct⟩, hcD⟩ hco
  set β : MulAut L := L.normalizerMonoidHom ⟨c, hCtN hct⟩ with hβdef
  have hβ : ∀ l : L, ((β l : L) : G) = c * l * c⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨c, hCtN hct⟩ l
  have hmem : ∀ {YC : Subgroup C} {x : C}, x ∈ YC →
      ((e.symm x : L) : G) ∈ (YC.map e.symm.toMonoidHom).map L.subtype :=
    fun {YC} {x} hx => ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
  have hfix : ∀ {YC : Subgroup C},
      c ∈ centralizer (((YC.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) →
      ∀ x ∈ YC, MulAut.congr e β x = x := by
    intro YC hc x hx
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    have h1 : β (e.symm x) = e.symm x := by
      apply Subtype.ext
      rw [hβ, ← mem_centralizer_iff.mp hc _ (hmem hx), mul_inv_cancel_right]
    rw [h1, MulEquiv.apply_symm_apply]
  obtain ⟨x₀, hx₀, hβx₀⟩ := hC _ (hfix hcX) (hfix hcD)
  set l₀ : G := ((e.symm x₀ : L) : G) with hl₀
  have hxl : ∀ y ∈ L, c * y * c⁻¹ = l₀ * y * l₀⁻¹ := by
    intro y hy
    have h1 : β = MulAut.conj (e.symm x₀) := by
      apply (MulAut.congr e).injective
      rw [hβx₀]
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    have h2 := congrArg (fun γ : MulAut L => ((γ ⟨y, hy⟩ : L) : G)) h1
    simp only [hβ, MulAut.conj_apply] at h2
    rw [h2]
    rfl
  rcases F4Pilot.eq_or_eq_mul_of_conj_eq htC ht hK hct (e.symm x₀).2 hxl with h | h
  · rw [h]
    exact hmem hx₀
  · exfalso
    have hl₀o : Odd (orderOf l₀) := by
      have h1 : orderOf l₀ = orderOf x₀ := by
        rw [hl₀, orderOf_submonoid, MulEquiv.orderOf_eq]
      have h2 : orderOf x₀ ∣ Nat.card XC := by
        have h3 := orderOf_dvd_natCard (⟨x₀, hx₀⟩ : XC)
        rw [← Subgroup.orderOf_coe] at h3
        exact h3
      rw [h1]
      exact hodd.of_dvd_nat h2
    have hcomm : Commute l₀ t := mem_centralizer_iff.mp htC l₀ (e.symm x₀).2
    set N := orderOf c * orderOf l₀ with hN
    have hNo : Odd N := hco.mul hl₀o
    have hcN : c ^ N = 1 := by rw [hN, pow_mul, pow_orderOf_eq_one, one_pow]
    have hlN : l₀ ^ N = 1 := by rw [hN, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have htN : t ^ N = t := by
      obtain ⟨k, hk⟩ := hNo
      have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
      rw [hk, pow_succ, pow_mul, ht2, one_pow, one_mul]
    have h1 : t = 1 := by
      have := hcN
      rw [h, hcomm.mul_pow, hlN, one_mul, htN] at this
      exact this
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)

end Transport

section TransportCoordinates

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]


theorem mem_of_odd_of_commute_pairTorus {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 5 ≤ n) (k : Fin n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {X D : Subgroup G}
    (hXe : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X := by
  subst hXe hDe
  obtain ⟨f, hKf⟩ := exists_card_eq_two_pow (K := K)
  exact mem_of_odd_of_commute_of_mulEquiv e (odd_card_pairTorus hKf k)
    (fun β hX hD => exists_mem_pairTorus_eq_conj hq hn k hX hD) htC ht hCtN hK


theorem mem_of_odd_of_commute_minusPairTorus {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_four_le hn) b c))
    {X D : Subgroup G}
    (hXe : X = ((minusPairTorus (K := K) (one_le_of_four_le hn) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((minusPairPerp (K := K) (one_le_of_four_le hn) b c k).map
      e.symm.toMonoidHom).map L.subtype) :
    ∀ x ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf x) → x ∈ X := by
  subst hXe hDe
  obtain ⟨f, hKf⟩ := exists_card_eq_two_pow (K := K)
  exact mem_of_odd_of_commute_of_mulEquiv e (odd_card_minusPairTorus hKf _ b c k)
    (fun β hX hD => exists_mem_minusPairTorus_eq_conj hq hn hirr k hX hD) htC ht hCtN hK

end TransportCoordinates

end CFSG.SeitzReduction.OmegaPilot
