module

public import CFSG.ClassicalInvolution.Asc77.AscL62Aut
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups commutatorElement

section SL23

@[expose] def elem3 : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩

theorem elem3_pow : elem3 ^ 3 = 1 := by decide +kernel

theorem sl23_eq_elem3 : ∀ g : SL(2, ZMod 3), g ^ 3 = 1 →
    (∀ p : SL(2, ZMod 3), p ^ 4 = 1 → g * p * g⁻¹ = elem3 * p * elem3⁻¹) → g = elem3 := by
  decide +kernel

theorem sl23_decomp : ∀ s : SL(2, ZMod 3), ∃ p : SL(2, ZMod 3), p ^ 4 = 1 ∧
    (s = p ∨ s = p * elem3 ∨ s = p * elem3 * elem3) := by
  decide +kernel

theorem sl23_card : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem sl23_card_four :
    (Finset.univ.filter (fun p : SL(2, ZMod 3) => p ^ 4 = 1)).card = 8 := by
  decide +kernel

theorem sl23_pow24 : ∀ s : SL(2, ZMod 3), s ^ 24 = 1 := by decide +kernel

theorem sl23_pow_four_of_pow_eight : ∀ s : SL(2, ZMod 3), s ^ 8 = 1 → s ^ 4 = 1 := by
  decide +kernel

theorem sl23_pow_four_of_two_pow {s : SL(2, ZMod 3)} {k : ℕ} (h : s ^ 2 ^ k = 1) : s ^ 4 = 1 := by
  refine sl23_pow_four_of_pow_eight s ?_
  have h1 : orderOf s ∣ 24 := orderOf_dvd_of_pow_eq_one (sl23_pow24 s)
  have h2 : orderOf s ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have h3 : a ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 4 ∣ orderOf s := by rw [ha]; exact pow_dvd_pow 2 hlt
    have := this.trans h1
    omega
  exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ha]; exact (pow_dvd_pow 2 h3 : 2 ^ a ∣ 2 ^ 3))

theorem mem_sylow_sl23 (P : Sylow 2 SL(2, ZMod 3)) {s : SL(2, ZMod 3)} (hs : s ^ 4 = 1) :
    s ∈ P := by
  classical
  have hcard : Nat.card P = 8 := by
    rw [Sylow.card_eq_multiplicity, sl23_card]
    have : (24 : ℕ).factorization 2 = 3 := by
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.factorization_eq_zero_of_not_dvd]
    rw [this]
    norm_num
  set T : Finset SL(2, ZMod 3) := Finset.univ.filter (fun p => p ∈ P) with hT
  set F : Finset SL(2, ZMod 3) := Finset.univ.filter (fun p : SL(2, ZMod 3) => p ^ 4 = 1)
    with hF
  have hTF : T ⊆ F := by
    intro x hx
    rw [hT, Finset.mem_filter] at hx
    rw [hF, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx.2⟩
    exact sl23_pow_four_of_two_pow (congrArg Subtype.val hk)
  have hTcard : T.card = 8 := by
    rw [← hcard, Nat.card_eq_fintype_card, hT, ← Fintype.card_subtype]
    rfl
  have hTeq : T = F := Finset.eq_of_subset_of_card_le hTF (by rw [hTcard, hF, sl23_card_four])
  have hsF : s ∈ F := by rw [hF, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hs⟩
  rw [← hTeq, hT, Finset.mem_filter] at hsF
  exact hsF.2

theorem sl23_hom_eq_of_fixes (α : SL(2, ZMod 3) →* SL(2, ZMod 3))
    (hα : ∀ p : SL(2, ZMod 3), p ^ 4 = 1 → α p = p) (s : SL(2, ZMod 3)) : α s = s := by
  have hc : α elem3 = elem3 := by
    refine sl23_eq_elem3 _ (by rw [← map_pow, elem3_pow, map_one]) fun p hp => ?_
    have h1 : (elem3 * p * elem3⁻¹) ^ 4 = 1 := by rw [conj_pow, hp]; group
    calc α elem3 * p * (α elem3)⁻¹ = α (elem3 * p * elem3⁻¹) := by
          rw [map_mul, map_mul, map_inv, hα p hp]
      _ = elem3 * p * elem3⁻¹ := hα _ h1
  obtain ⟨p, hp, h | h | h⟩ := sl23_decomp s
  · rw [h, hα p hp]
  · rw [h, map_mul, hα p hp, hc]
  · rw [h, map_mul, map_mul, hα p hp, hc]

end SL23

section M3

@[expose] noncomputable def slEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (MonoidHom.ext fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp)
    (MonoidHom.ext fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp)

theorem mulAut_eq_one_of_fixes_sylow_three (P : Sylow 2 SL(2, GaloisField 3 1))
    (β : MulAut SL(2, GaloisField 3 1)) (hfix : ∀ x ∈ P, β x = x) : β = 1 := by
  set ψ : SL(2, GaloisField 3 1) ≃* SL(2, ZMod 3) :=
    slEquiv (GaloisField.equivZmodP 3).toRingEquiv with hψ
  let α : SL(2, ZMod 3) →* SL(2, ZMod 3) :=
    (ψ.toMonoidHom.comp (β : SL(2, GaloisField 3 1) →* SL(2, GaloisField 3 1))).comp
      ψ.symm.toMonoidHom
  let P' : Sylow 2 SL(2, ZMod 3) := Sylow.mapSurjective (f := ψ.toMonoidHom) ψ.surjective P
  have hα : ∀ p : SL(2, ZMod 3), p ^ 4 = 1 → α p = p := by
    intro p hp
    have hpP : p ∈ P' := mem_sylow_sl23 P' hp
    have hpP' : p ∈ (P : Subgroup SL(2, GaloisField 3 1)).map ψ.toMonoidHom := by
      rw [← Sylow.coe_mapSurjective (f := ψ.toMonoidHom) ψ.surjective P]
      exact hpP
    obtain ⟨x, hx, rfl⟩ := hpP'
    change ψ (β (ψ.symm (ψ x))) = ψ x
    rw [MulEquiv.symm_apply_apply, hfix x hx]
  ext x : 1
  have h1 := sl23_hom_eq_of_fixes α hα (ψ x)
  change ψ (β (ψ.symm (ψ x))) = ψ x at h1
  rw [MulEquiv.symm_apply_apply] at h1
  exact ψ.injective h1


end M3

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
