module

public import CFSG.ClassicalInvolution.Uniform.UTwin
public import CFSG.ClassicalInvolution.Asc77.AscHypOmegaTwin

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ClassicalInvolution.Generic.CoreAssembly
open scoped MatrixGroups commutatorElement

section Count

variable {G : Type} [Group G] [Finite G]

theorem padicValNat_card_inf_le_one_of_commutator {K J : Subgroup G}
    (hcomm : ⁅K, J⁆ ≤ oddCoreOf K)
    (hZ : Nat.card (Subgroup.center (K ⧸ classicalInvolutionOddCore K)) = 2) :
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 := by
  set N : Subgroup ↥K := classicalInvolutionOddCore ↥K with hN
  set A : Subgroup ↥K := (K ⊓ J).subgroupOf K with hA
  have hAcard : Nat.card A = Nat.card ↥(K ⊓ J) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  let φ : ↥A →* K ⧸ N := (QuotientGroup.mk' N).comp A.subtype
  have hrange : φ.range ≤ Subgroup.center (K ⧸ N) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have haJ : ((a : ↥K) : G) ∈ J := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp a.2)).2
    have h1 : ⁅(k : G), ((a : ↥K) : G)⁆ ∈ ⁅K, J⁆ := Subgroup.commutator_mem_commutator k.2 haJ
    obtain ⟨c, hcN, hc⟩ := hcomm h1
    have hck : c = ⁅k, (a : ↥K)⁆ := Subtype.ext (by
      have hc' : (c : G) = ⁅(k : G), ((a : ↥K) : G)⁆ := hc
      rw [hc']
      simp [commutatorElement_def])
    rw [hck] at hcN
    have h4 : ((⁅k, (a : ↥K)⁆ : ↥K) : K ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr hcN
    have h5 : ⁅(k : K ⧸ N), ((a : ↥K) : K ⧸ N)⁆ = 1 := by
      simpa [commutatorElement_def] using h4
    exact commutatorElement_eq_one_iff_mul_comm.mp h5
  have hker : Odd (Nat.card φ.ker) := by
    have hdvd : Nat.card φ.ker ∣ Nat.card N := by
      refine Subgroup.card_dvd_of_injective
        (MonoidHom.codRestrict ((A.subtype).comp φ.ker.subtype) N ?_) ?_
      · intro x
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx
        exact (QuotientGroup.eq_one_iff _).mp hx
      · intro x y hxy
        have := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext this)
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥K).of_dvd_nat hdvd
  have hrng : Nat.card φ.range ∣ 2 := by
    rw [← hZ]
    exact Subgroup.card_dvd_of_le hrange
  have hmul := Subgroup.card_ker_mul_card_range φ
  have hker0 : Nat.card φ.ker ≠ 0 := Nat.card_pos.ne'
  have hrng0 : Nat.card φ.range ≠ 0 := Nat.card_pos.ne'
  rw [← hAcard, ← hmul, padicValNat.mul hker0 hrng0,
    padicValNat.eq_zero_of_not_dvd (Nat.not_even_iff_odd.mpr hker |> fun h2 h3 =>
      h2 (even_iff_two_dvd.mpr h3)), zero_add]
  rcases (Nat.dvd_prime Nat.prime_two).mp hrng with h1 | h2
  · rw [h1]; simp
  · rw [h2]; simp

end Count

section Omega4

variable {t : MemberType} {G : Type} [Group G] [Finite G] {K₀ : Subgroup G} {z₀ : G}

theorem omega4_of_memberU (hc : t.Cert) (h₀ : IsClassicalMemberU t K₀ z₀)
    (hint : IsIntrinsicU t K₀ z₀) {K J : Subgroup G} (hK : K ∈ conjClass K₀)
    (hJ : J ∈ conjClass K₀) (hne : K ≠ J) :
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J) := by
  obtain ⟨a, rfl⟩ := single_class K₀ K hK
  obtain ⟨b, rfl⟩ := single_class K₀ J hJ
  have hKa := h₀.conj a
  have hJb := h₀.conj b
  have hUa := hKa.isUniqueInvolution hc
  have hUb := hJb.isUniqueInvolution hc
  by_cases h2 : 2 ∣ Nat.card ↥(conjSub a K₀ ⊓ conjSub b K₀)
  ·
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
    have hu1 : (u : G) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hu'
      omega
    have huu : (u : G) * u = 1 := by rw [← sq, ← hu', pow_orderOf_eq_one]
    have ha := (hUa.unique u (Subgroup.mem_inf.mp u.2).1 huu).resolve_left hu1
    have hb := (hUb.unique u (Subgroup.mem_inf.mp u.2).2 huu).resolve_left hu1
    have hJb' : IsClassicalMemberU t (conjSub b K₀) (a * z₀ * a⁻¹) := by
      rw [← ha, hb]
      exact hJb
    have hiJ : IsIntrinsicU t (conjSub b K₀) (a * z₀ * a⁻¹) := by
      rw [← ha, hb]
      exact hint.conj b
    obtain ⟨-, -, hcomm, -⟩ := twins_of_memberU hKa hJb' (hint.conj a) hiJ hne
    exact ⟨padicValNat_card_inf_le_one_of_commutator (hcomm.trans inf_le_left)
      hKa.natCard_center_eq_two, fun _ => hcomm⟩
  · rw [padicValNat.eq_zero_of_not_dvd h2]
    exact ⟨Nat.zero_le _, fun h => absurd h (by norm_num)⟩


theorem omega5_of_omega5AtU (hc : t.Cert) (h₀ : IsClassicalMemberU t K₀ z₀)
    (h5 : Omega5At (conjClass K₀) K₀ z₀) :
    ∀ K ∈ conjClass K₀, ∀ J ∈ conjClass K₀, K ≠ J → ∀ z : G,
      IsUniqueInvolution K z → ∀ v ∈ J, (¬ ∀ w ∈ J, v * w = w * v) →
        IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
          v ∈ Subgroup.normalizer (K : Set G) := by
  intro K hK J hJ hKJ z hz v hvJ hvnc hv2 hvz
  obtain ⟨a, rfl⟩ := single_class K₀ K hK
  have hUa := (h₀.conj a).isUniqueInvolution hc
  have hza : a * z₀ * a⁻¹ = z := hUa.eq hz
  have hJ' : conjSub a⁻¹ J ∈ conjClass K₀ := by
    obtain ⟨b, rfl⟩ := single_class K₀ J hJ
    exact ⟨a⁻¹ * b, conjSub_mul a⁻¹ b K₀⟩
  have hne' : K₀ ≠ conjSub a⁻¹ J := by
    intro h
    apply hKJ
    have := congrArg (conjSub a) h
    rwa [conjSub_conjSub_inv] at this
  have hv' : a⁻¹ * v * a ∈ conjSub a⁻¹ J := by
    simpa using conj_mem_conjSub (n := a⁻¹) hvJ
  have hnc' : ¬ ∀ w ∈ conjSub a⁻¹ J, (a⁻¹ * v * a) * w = w * (a⁻¹ * v * a) := by
    intro h
    apply hvnc
    intro w hw
    have hw' : a⁻¹ * w * a ∈ conjSub a⁻¹ J := by simpa using conj_mem_conjSub (n := a⁻¹) hw
    have := h _ hw'
    calc v * w = a * ((a⁻¹ * v * a) * (a⁻¹ * w * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * w * a) * (a⁻¹ * v * a)) * a⁻¹ := by rw [this]
      _ = w * v := by group
  have hv2' : IsPGroup 2 (Subgroup.zpowers (a⁻¹ * v * a)) := by
    have := isPGroup_zpowers_conj hv2 a⁻¹
    rwa [inv_inv] at this
  have hz₀ : z₀ = a⁻¹ * z * a := by rw [← hza]; group
  have hvz' : (a⁻¹ * v * a) * z₀ = z₀ * (a⁻¹ * v * a) := by
    rw [hz₀]
    calc a⁻¹ * v * a * (a⁻¹ * z * a) = a⁻¹ * (v * z) * a := by group
      _ = a⁻¹ * (z * v) * a := by rw [hvz]
      _ = a⁻¹ * z * a * (a⁻¹ * v * a) := by group
  have hn := h5 _ hJ' hne' _ hv' hnc' hv2' hvz'
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro x
  have hx := hn (a⁻¹ * x * a)
  rw [mem_conjSub_iff, mem_conjSub_iff]
  have e : a⁻¹ * (v * x * v⁻¹) * a = (a⁻¹ * v * a) * (a⁻¹ * x * a) * (a⁻¹ * v * a)⁻¹ := by group
  rw [e]
  exact hx

end Omega4

end CFSG.ClassicalInvolution.Uniform
