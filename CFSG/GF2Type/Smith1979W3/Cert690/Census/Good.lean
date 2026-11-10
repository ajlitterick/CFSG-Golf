module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Elt
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Conj

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

@[expose] def GoodElt (minus : Bool) (L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (e : V₀)
    (x : V₀ ≃ₗ[ZMod 2] V₀) : Prop :=
  x ∈ O₀ minus ∧ (x e = e ↔ x ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))) ∧
    (x ∈ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) → x ^ 128 = 1)

theorem b0Of_lt (minus : Bool) : b0Of minus < 64 := by
  unfold b0Of
  by_cases h : 0 < (singOf minus).size
  · rw [array_getElem!_eq_getElem h]
    have hmem : (singOf minus)[0] ∈ (singOf minus).toList := array_getElem_mem_toList h
    simp only [singOf, List.toList_toArray, List.mem_filter, List.mem_range] at hmem
    exact hmem.1
  · rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?]
    simp [h]

noncomputable def censusN (minus : Bool) (L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (e : V₀) :
    Subgroup (V₀ ≃ₗ[ZMod 2] V₀) :=
  O₀ minus ⊓ MulAction.stabilizer (V₀ ≃ₗ[ZMod 2] V₀) e ⊓
    Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))

theorem mem_censusN {minus : Bool} {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {e : V₀}
    {n : V₀ ≃ₗ[ZMod 2] V₀} :
    n ∈ censusN minus L e ↔
      n ∈ O₀ minus ∧ n e = e ∧ n ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
  rw [censusN, Subgroup.mem_inf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    LinearEquiv.smul_def]
  exact and_assoc


theorem goodElt_of_censusCond {minus : Bool} {H L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {e : V₀}
    (hH : H ≤ O₀ minus) (hC : CensusCond minus H L e) {h : V₀ ≃ₗ[ZMod 2] V₀} (hh : h ∈ H) :
    GoodElt minus L e h := by
  obtain ⟨hLH, hfixL, hinvL, hcardL, hnorfix, h2grp⟩ := hC
  refine ⟨hH hh, (hnorfix h hh).symm, ?_⟩
  intro hcen
  have hsub : h ∈ H ⊓ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := ⟨hh, hcen⟩
  have hdvd : orderOf h ∣ Nat.card (O₀ minus) :=
    (Subgroup.orderOf_dvd_natCard _ hsub).trans
      (Subgroup.card_dvd_of_le (inf_le_left.trans hH))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2grp.exists_orderOf_eq_pow
    (⟨h, hsub⟩ : ↥(H ⊓ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))))
  have hk' : orderOf h = 2 ^ k := (Subgroup.orderOf_coe _).trans hk
  have h128 : orderOf h ∣ 128 := by
    cases minus
    · have hd : 2 ^ k ∣ 40320 := by
        rw [hk'] at hdvd
        rw [natCard_O₀] at hdvd
        simpa using hdvd
      have hcop : Nat.Coprime (2 ^ k) 315 :=
        (show Nat.Coprime 2 315 by norm_num).pow_left k
      have hd' : 2 ^ k ∣ 128 * 315 := by simpa using hd
      rw [hk']
      simpa using hcop.dvd_of_dvd_mul_right hd'
    · have hd : 2 ^ k ∣ 51840 := by
        rw [hk'] at hdvd
        rw [natCard_O₀] at hdvd
        simpa using hdvd
      have hcop : Nat.Coprime (2 ^ k) 405 :=
        (show Nat.Coprime 2 405 by norm_num).pow_left k
      have hd' : 2 ^ k ∣ 128 * 405 := by simpa using hd
      rw [hk']
      simpa using hcop.dvd_of_dvd_mul_right hd'
  exact orderOf_dvd_iff_pow_eq_one.mp h128

theorem goodElt_conj {minus : Bool} {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {e : V₀}
    {n : V₀ ≃ₗ[ZMod 2] V₀} (hn : n ∈ censusN minus L e) {x : V₀ ≃ₗ[ZMod 2] V₀}
    (hx : GoodElt minus L e x) : GoodElt minus L e (n⁻¹ * x * n) := by
  obtain ⟨hnO, hne, hnnor⟩ := mem_censusN.mp hn
  obtain ⟨hxO, hxfix, hxpow⟩ := hx
  have hneinv : n⁻¹ e = e := by
    calc
      n⁻¹ e = n⁻¹ (n e) := by rw [hne]
      _ = (n⁻¹ * n) e := (LinearEquiv.mul_apply _ _ _).symm
      _ = e := by simp
  have hval : (n⁻¹ * x * n) e = n⁻¹ (x e) := by
    simp [LinearEquiv.mul_apply, hne]
  have hfixiff : (n⁻¹ * x * n) e = e ↔ x e = e := by
    rw [hval]
    constructor
    · intro h
      have := congrArg (fun v => n v) h
      simpa [hne] using this
    · intro h
      rw [h, hneinv]
  have hconjSub : conjSub L n = L := by
    rw [conjSub]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hnnor
  have hnormiff : x ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) ↔
      n⁻¹ * x * n ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
    rw [← mem_normalizer_conjSub_iff (L := L) (g := n) (h := x), hconjSub]
  have hceniff : x ∈ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) ↔
      n⁻¹ * x * n ∈ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
    have hc : conjSub (Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))) n =
        Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
      rw [← centralizer_conjSub, hconjSub]
    rw [← mem_conjSub (H := Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)))
      (g := n) (x := x), hc]
  refine ⟨mul_mem (mul_mem (inv_mem hnO) hxO) hnO,
    hfixiff.trans (hxfix.trans hnormiff), ?_⟩
  intro hc
  have hpx : x ^ 128 = 1 := hxpow (hceniff.mpr hc)
  have hpow : (n⁻¹ * x * n) ^ 128 = n⁻¹ * x ^ 128 * n := by
    simpa using conj_pow (a := n⁻¹) (b := x) (i := 128)
  rw [hpow, hpx]
  simp

end CFSG.GF2Type.Smith1979W3.Cert690

end
