module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStmt
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Field
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KGD.D4T36Frame
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Generic

variable {Y : Type} [Group Y]


theorem d4_inner_fix_trivial {Y : Type} [Group Y] (hcen : Subgroup.center Y = ⊥) (φ : MulAut Y)
    (hA : D4NoAbel φ) (ζ : MulAut Y) (hζ : ζ ∈ (MulAut.conj : Y →* MulAut Y).range)
    (hcomm : ζ * φ = φ * ζ) (hfix : ∀ c ∈ fixSub φ, ζ c = c) : ζ = 1 := by
  obtain ⟨z, rfl⟩ := hζ
  have hinj := mulAut_conj_injective_of_center_eq_bot hcen
  have hφz : φ z = z := by
    apply hinj
    rw [← mulAut_conj_conj φ z]
    calc φ * MulAut.conj z * φ⁻¹ = MulAut.conj z * φ * φ⁻¹ := by rw [← hcomm]
      _ = MulAut.conj z := by group
  have hzF : z ∈ fixSub φ := mem_fixSub.2 hφz
  have hcenter : (⟨z, hzF⟩ : ↥(fixSub φ)) ∈ Subgroup.center ↥(fixSub φ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 := hfix g g.2
    simp only [MulAut.conj_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hbot := hA (Subgroup.center ↥(fixSub φ)) inferInstance (fun x y =>
    Subtype.ext ((Subgroup.mem_center_iff.1 y.2) (x : ↥(fixSub φ))))
  rw [hbot, Subgroup.mem_bot] at hcenter
  have hz1 : z = 1 := congrArg Subtype.val hcenter
  rw [hz1, map_one]


end Generic

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section OrderBound

theorem d4_card_fixSub_fieldActor {p f r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hr : r.Prime) (hr3 : 3 < r) (hrf : r ∣ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (η : K ≃+* K) (hη : orderOf η = r) :
    ∃ M : ℕ, ¬ p ∣ M ∧
      Nat.card (fixSub (fieldActor (t := TwistTag.D4) σ η)) = (p ^ (f / r)) ^ 12 * M := by
  classical
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, hcyc, hcard, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨d, hd⟩ : ∃ d, f = d * r := ⟨f / r, (Nat.div_mul_cancel hrf).symm⟩
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, zero_mul] at hd
      omega
    · exact h0
  have hr2 : 2 ≤ r := hr.two_le
  have hm3 : Nat.Coprime r 3 := (Nat.coprime_primes hr Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = p ^ (3 * d * r) := by rw [hK3, hd, mul_assoc]
  have hσ' : ∀ c, σ c = c ^ p ^ (d * r) := fun c => by rw [hσ c, hd]
  set δ : K ≃+* K := iterateFrobeniusEquiv K p (3 * d) with hδdef
  have hδ : ∀ c, δ c = c ^ p ^ (3 * d) := fun c => by
    rw [hδdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, hδord, -, hcardFix, -⟩ := triality_canonical_field_facts hp hd1 hr2 hm3 hK' hσ' hδ
  obtain ⟨-, -, -, -, -, -, h7, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hp hd1 hr2 hm3 K hK' σ hσ' δ hδ
  have hδpow : δ ^ r = 1 := by rw [← hδord]; exact pow_orderOf_eq_one δ
  have hηpow : η ^ r = 1 := by rw [← hη]; exact pow_orderOf_eq_one η
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have := hcyc
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic hr.pos hδord hηpow))
  replace hk : δ ^ k = η := hk
  obtain ⟨s, -, hs⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic hr.pos hη hδpow))
  replace hs : η ^ s = δ := hs
  set α₀ : MulAut C := fieldActor σ δ with hα₀
  set φ' : MulAut C := fieldActor σ η with hφ'
  have hφ'α : φ' = α₀ ^ k := by
    rw [hφ', hα₀, ← hk]
    exact map_pow (fieldActorHom (t := TwistTag.D4) σ) δ k
  have hαφ' : α₀ = φ' ^ s := by
    rw [hα₀, hφ', ← hs]
    exact map_pow (fieldActorHom (t := TwistTag.D4) σ) η s
  have hfix : fixSub φ' = fixSub α₀ :=
    le_antisymm (hαφ' ▸ fixSub_le_fixSub_pow φ' s) (hφ'α ▸ fixSub_le_fixSub_pow α₀ k)
  set L := fixSubfield δ with hLdef
  have hLcard : Nat.card L = (p ^ d) ^ 3 := by rw [hcardFix, mul_comm, pow_mul]
  obtain ⟨ρ, hρ, t, hrt⟩ : ∃ ρ, (ρ = 1 ∨ ρ = 2) ∧ ∃ t, r = 3 * t + ρ := by
    have h3 : r % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    exact ⟨r % 3, by omega, r / 3, by omega⟩
  have hσL : ∀ c : L, fixSubfieldRestrict σ δ c = c ^ ((p ^ d) ^ ρ) := by
    intro c
    apply Subtype.ext
    have hc : (c : K) ^ p ^ (3 * d) = c := by rw [← hδ]; exact c.2
    rw [coe_fixSubfieldRestrict, hσ' _, SubmonoidClass.coe_pow]
    set x : K := (c : K) ^ ((p ^ d) ^ ρ) with hx
    have hxfix : x ^ p ^ (3 * d) = x := by
      rw [hx, ← pow_mul, mul_comm, pow_mul, hc]
    have hiter : ∀ n : ℕ, x ^ ((p ^ (3 * d)) ^ n) = x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, pow_mul, ih, hxfix]
    have hexp : p ^ (d * r) = (p ^ d) ^ ρ * (p ^ (3 * d)) ^ t := by
      have : d * r = d * ρ + 3 * d * t := by rw [hrt]; ring
      rw [this, pow_add, pow_mul, pow_mul]
    rw [hexp, pow_mul, ← hx, hiter]
  have hord := (triality_both_orientations_exact_finite_order p d hp hd1 L hLcard ρ hρ
    (fixSubfieldRestrict σ δ).toRingHom (fun c => hσL c)).1
  have hJ : Nat.card (fixSub φ') = Nat.card (graphFixedRootGroup TwistTag.D4 L
      (fixSubfieldRestrict σ δ).toRingHom) := by
    rw [hfix]
    have h1 : Nat.card (fixSub α₀) = Nat.card ((fixSub α₀).map C.subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).toEquiv
    have h2 : (fixSub α₀).map C.subtype = trialityFieldImage σ δ := h7
    have h3 : Nat.card (trialityFieldImage σ δ) = Nat.card (graphFixedRootGroup TwistTag.D4 L
        (fixSubfieldRestrict σ δ).toRingHom) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _)).toEquiv.symm
    rw [h1, h2, h3]
  refine ⟨((p ^ d) ^ 2 - 1) * ((p ^ d) ^ 6 - 1) * ((p ^ d) ^ 8 + (p ^ d) ^ 4 + 1), ?_, ?_⟩
  · have hpa : p ∣ p ^ d := dvd_pow_self p (by omega)
    have hpm : ∀ n : ℕ, 1 ≤ n → ¬ p ∣ (p ^ d) ^ n - 1 := by
      intro n hn h
      have h1 : p ∣ (p ^ d) ^ n := dvd_pow hpa (by omega)
      have h2 : 1 ≤ (p ^ d) ^ n := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hp.pos)
      have h3 := Nat.dvd_sub h1 h
      have h4 : (p ^ d) ^ n - ((p ^ d) ^ n - 1) = 1 := by omega
      rw [h4] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
    intro hpM
    rcases hp.dvd_mul.1 hpM with h | h
    · rcases hp.dvd_mul.1 h with h | h
      · exact hpm 2 (by norm_num) h
      · exact hpm 6 (by norm_num) h
    · have h1 : p ∣ (p ^ d) ^ 8 + (p ^ d) ^ 4 := dvd_add (dvd_pow hpa (by norm_num))
        (dvd_pow hpa (by norm_num))
      exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 h))
  · rw [show f / r = d by rw [hd]; exact Nat.mul_div_cancel d hr.pos, hJ, hord]
    ring

end OrderBound

section PtKer

theorem d4PtKer_of_noAbel_pgroup {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hA : D4NoAbel φ)
    (U₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hU : U₀ ≤ fixSub φ)
    (hUp : IsPGroup p U₀) (hcard : (p ^ f) ^ 3 ≤ Nat.card U₀) : D4PtKer φ := by
  classical
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, ⟨Θ, hΘ, -, hΘker, -⟩, -, hcardAut, -, hcen, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  intro ζ hodd hcop hcomm hfix
  have hpowcomm : ∀ n : ℕ, ζ ^ n * φ = φ * ζ ^ n := fun n =>
    (Commute.pow_left (show Commute ζ φ from hcomm) n).eq
  have hpowfix : ∀ n : ℕ, ∀ c ∈ fixSub φ, (ζ ^ n) c = c := by
    intro n
    induction n with
    | zero => intro c _; rw [pow_zero]; rfl
    | succ n ih => intro c hc; rw [pow_succ, MulAut.mul_apply, hfix c hc, ih c hc]
  set m := orderOf (Θ ζ) with hm
  have hζm : ζ ^ m = 1 := by
    have h1 : Θ (ζ ^ m) = 1 := by rw [map_pow]; exact pow_orderOf_eq_one _
    have hmem : ζ ^ m ∈ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range := by rw [← hΘker]; exact h1
    exact d4_inner_fix_trivial hcen φ hA _ hmem (hpowcomm m) (hpowfix m)
  have hmdvd : m ∣ orderOf ζ := orderOf_map_dvd Θ ζ
  have hzord : orderOf ζ = m := Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hζm) hmdvd
  by_cases hm1 : m = 1
  · rw [hm1, pow_one] at hζm
    exact hζm
  exfalso
  have hm0 : 0 < m := orderOf_pos _
  have hmodd : Odd m := hzord ▸ hodd
  have hmcop : Nat.Coprime m 3 := hzord ▸ hcop
  set r := Nat.minFac m with hrdef
  have hr : r.Prime := Nat.minFac_prime hm1
  have hrm : r ∣ m := Nat.minFac_dvd m
  have hr2 : r ≠ 2 := fun h => by
    rw [h] at hrm
    exact (Nat.not_even_iff_odd.2 hmodd) (even_iff_two_dvd.2 hrm)
  have hr3' : r ≠ 3 := fun h => by
    rw [h] at hrm
    exact absurd (Nat.Coprime.eq_one_of_dvd hmcop.symm hrm) (by norm_num)
  have hr3 : 3 < r := by have := hr.two_le; omega
  have hdiv : m / r ∣ m := Nat.div_dvd_of_dvd hrm
  have hdpos : 0 < m / r := Nat.div_pos (Nat.le_of_dvd hm0 hrm) hr.pos
  set ζ' := ζ ^ (m / r) with hζ'
  have hζ'ord : orderOf ζ' = r := by
    rw [hζ', orderOf_pow_of_dvd hdpos.ne' (hzord ▸ hdiv), hzord, Nat.div_div_self hrm hm0.ne']
  have hζ'out : ζ' ∉ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range := by
    intro hmem
    rw [← hΘker, MonoidHom.mem_ker, hζ', map_pow] at hmem
    have h1 := orderOf_dvd_of_pow_eq_one hmem
    have h2 : m / r < m := Nat.div_lt_self hm0 hr.one_lt
    exact absurd (Nat.le_of_dvd hdpos h1) (by omega)
  obtain ⟨hηord, hrf, ⟨g₀, hg₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial hp hf K hK σ hσ Θ hΘ hr hr3
      ⊤ le_top ⟨ζ', Subgroup.mem_top _⟩ hζ'out (by rw [Subgroup.orderOf_mk]; exact hζ'ord)
  obtain ⟨M, hpM, hMcard⟩ := d4_card_fixSub_fieldActor hp hp2 hf hr hr3 hrf K hK σ hσ (Θ ζ') hηord
  have hU₁ : U₀.map (MulAut.conj g₀).toMonoidHom ≤
      fixSub (fieldActor (t := TwistTag.D4) σ (Θ ζ')) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixSub, ← hg₀]
    have hxfix := hpowfix (m / r) x (hU hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [show ζ' x = x from hxfix]
  obtain ⟨a, ha⟩ := hUp.exists_card_eq
  have hcardU₁ : Nat.card (U₀.map (MulAut.conj g₀).toMonoidHom) = Nat.card U₀ :=
    (Nat.card_congr (Subgroup.equivMapOfInjective U₀ (MulAut.conj g₀).toMonoidHom
      (MulAut.conj g₀).injective).toEquiv).symm
  have hdvd := Subgroup.card_dvd_of_le hU₁
  rw [hcardU₁, ha, hMcard] at hdvd
  have hcopM : Nat.Coprime (p ^ a) M :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
  have hdvd2 : p ^ a ∣ (p ^ (f / r)) ^ 12 := hcopM.dvd_of_dvd_mul_right hdvd
  rw [← pow_mul] at hdvd2
  have hle : a ≤ f / r * 12 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd2
  have h3f : f * 3 ≤ a := by
    rw [ha, ← pow_mul] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  obtain ⟨d, hd⟩ := hrf
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, mul_zero] at hd
      omega
    · exact h0
  have hr5 : 5 ≤ r := by
    by_contra h
    have h4 : r = 4 := by omega
    rw [h4] at hr
    exact absurd hr (by norm_num)
  rw [hd, Nat.mul_div_cancel_left d hr.pos] at hle
  rw [hd] at h3f
  nlinarith


end PtKer

end CFSG.GH74.GLS.Stage2.Bender.Thm1
